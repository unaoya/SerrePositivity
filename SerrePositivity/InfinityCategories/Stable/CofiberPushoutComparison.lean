module
public import SerrePositivity.InfinityCategories.Stable.PushoutCofiberRectangle
public import SerrePositivity.InfinityCategories.Stable.CofiberSquareComparisonIso
public import SerrePositivity.InfinityCategories.Stable.SuspensionSpanComparison

/-! # 押し出しに沿う二つの実 cofiber の比較

概要：押し出し四角形の左右の辺は、同じ実 cofiber 頂点を持つ四角形を選べる。
方針：零終点の長方形の外側と右面を転置し、指定辺を厳密に照合する。
規約：実四角形と余極限性を保持。使われ方：Verdier 分母の基底変更。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 転置した四角形の底辺は元の左辺。 -/
lemma squareBottomEdge_transpose :
    squareBottomEdge ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom = squareLeftEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

variable {X : SSet.{u}} {L : Δ[1] ⊗ Δ[1] ⟶ X}

/-- 零終点長方形の外側は、元の左辺の実 cofiber 四角形。 -/
def PushoutCofiberRectangle.leftCofiberSquare (r : PushoutCofiberRectangle L) :
    CofiberSquare (squareLeftArrow L) where
  toZeroTriangle := r.outerZeroTriangle
  bottom_edge := by
    change squareBottomEdge ≫ ((β_ Δ[1] Δ[1]).hom ≫ pastingSquare r.diagram 1) = _
    rw [← Category.assoc, squareBottomEdge_transpose, pastingSquare_outer_leftEdge,
      r.left_eq, squareLeftArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply _).symm
  isPushout := r.outer_isCofiber

/-- 零終点長方形の右面は、元の右辺の実 cofiber 四角形。 -/
def PushoutCofiberRectangle.rightCofiberSquare (r : PushoutCofiberRectangle L) :
    CofiberSquare (squareRightArrow L) where
  toZeroTriangle := r.rightZeroTriangle
  bottom_edge := by
    change squareBottomEdge ≫ ((β_ Δ[1] Δ[1]).hom ≫ pastingSquare r.diagram 0) = _
    rw [← Category.assoc, squareBottomEdge_transpose, ← pastingSquare_sharedEdge,
      r.left_eq, squareRightArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply _).symm
  isPushout := r.right_isCofiber

/-- 二つの実 cofiber 四角形の cofiber 頂点は厳密に同じ。 -/
lemma PushoutCofiberRectangle.cofiber_eq (r : PushoutCofiberRectangle L) :
    r.leftCofiberSquare.cofiber = r.rightCofiberSquare.cofiber := rfl

/-- 左右の辺の任意の実 cofiber 対象は、押し出しに沿って実同型になる。 -/
def cofiberPushoutComparisonIso [Quasicategory X] [IsStable X]
    (hL : IsPushoutSquare L) (s : CofiberSquare (squareLeftArrow L))
    (t : CofiberSquare (squareRightArrow L)) : VertexIso s.cofiber t.cofiber := by
  let r := chosenPushoutCofiberRectangle L hL
  exact cofiberSquareComparisonIso s r.leftCofiberSquare ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk r.cofiber_eq) ≪≫
      cofiberSquareComparisonIso r.rightCofiberSquare t

end SerrePositivity.InfinityCategories
