module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutCofiberRectangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquareComparisonIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSpanComparison

/-! # 押し出しに沿う二つの実 cofiber の比較

概要：押し出し四角形の左右の辺は、同じ実 cofiber 頂点を持つ四角形を選べる。
方針：零終点の長方形の外側と右面を転置し、指定辺を厳密に照合する。
規約：実四角形と余極限性を保持。使われ方：Verdier 分母の基底変更。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 転置した四角形の底辺は元の左辺。 -/
lemma squareBottomEdge_transpose :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

variable {X : SSet.{u}} {L : Δ[1] ⊗ Δ[1] ⟶ X}

/-- 零終点長方形の外側は、元の左辺の実 cofiber 四角形。 -/
def PushoutCofiberRectangle.leftCofiberSquare (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutCofiberRectangle L) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow L) where
  toZeroTriangle := r.outerZeroTriangle
  bottom_edge := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ ((β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 1) = _
    rw [← Category.assoc, squareBottomEdge_transpose, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_outer_leftEdge,
      r.left_eq, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply _).symm
  isPushout := r.outer_isCofiber

/-- 零終点長方形の右面は、元の右辺の実 cofiber 四角形。 -/
def PushoutCofiberRectangle.rightCofiberSquare (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutCofiberRectangle L) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow L) where
  toZeroTriangle := r.rightZeroTriangle
  bottom_edge := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ ((β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 0) = _
    rw [← Category.assoc, squareBottomEdge_transpose, ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_sharedEdge,
      r.left_eq, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply _).symm
  isPushout := r.right_isCofiber

/-- 二つの実 cofiber 四角形の cofiber 頂点は厳密に同じ。 -/
lemma PushoutCofiberRectangle.cofiber_eq (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutCofiberRectangle L) :
    r.leftCofiberSquare.cofiber = r.rightCofiberSquare.cofiber := rfl

/-- 左右の辺の任意の実 cofiber 対象は、押し出しに沿って実同型になる。 -/
def cofiberPushoutComparisonIso [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare L) (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow L))
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow L)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso s.cofiber t.cofiber := by
  let r := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenPushoutCofiberRectangle L hL
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSquareComparisonIso s r.leftCofiberSquare ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk r.cofiber_eq) ≪≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSquareComparisonIso r.rightCofiberSquare t

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.2.4.14" (partial := direction) "仮定：安定準圏と引き戻し正方形に対する余ファイバー長方形（HA の一方向）。結論：引き戻しは押し出しなので、二つの余ファイバーの hC 上の同型が得られる。誘導射の可逆性から引き戻しを得る逆向きは採用した型にない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberPushoutComparisonIso
