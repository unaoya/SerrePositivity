module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroEndPasting
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareDuality
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingComparisonHomotopy

/-! # Cofiber 列の回転長方形

概要：cofiber 列を右に零対象を付加した長方形へ延長し、右側の回転列と外側の suspension を得る。
方針：終対象への合成二単体を付加し、押し出しの貼り合わせで二つの普遍性を得る。
規約：元の列を厳密に保持。使われ方：三角形の回転の幾何学的構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：cofiber 列の右に零対象を付加した両側押し出しの長方形。
方針：左面の厳密な一致、右下の零性、右面と外側の押し出し性を保持する。
規約：入力 t の押し出し性は存在定理で使う。使われ方：回転列と suspension の同時指定。 -/
structure CofiberRotationRectangle {X : SSet.{u}} (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) where
  diagram : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X
  left_eq : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 2 = t.square
  zero_end : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 0) 1 0)
  right_isPushout : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 0)
  outer_isPushout : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare diagram 1)

/-- 概要：安定な quasicategory の任意の cofiber 列は回転長方形へ延長できる。
方針：指定した零対象へ向かう底辺二単体を選び、零終点の押し出し長方形へ延長する。
規約：左の四角形は入力と厳密に同じ。使われ方：回転長方形の存在。 -/
lemma nonempty_cofiberRotationRectangle {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) : Nonempty (CofiberRotationRectangle t) := by
  let z := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X
  obtain ⟨τ, hτ, hlast⟩ :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_terminalCompositeTriangle z.isTerminal (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow t.square)
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square = stdSimplex.δ (2 : Fin 3) ≫ τ := by
    rw [hτ, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square)).symm
  have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (τ.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (2 : Fin 3))) := by
    rw [hlast]
    exact z.isZero
  obtain ⟨F, hleft, hbottom, hright, houter⟩ :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_pushoutRectangle_of_zeroEnd t.square ht τ h hz
  refine ⟨⟨F, hleft, ?_, hright, houter⟩⟩
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle F).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (2 : Fin 3)))
  rw [hbottom]
  exact hz

/-- 概要：安定な quasicategory の cofiber 列の回転長方形を一つ選ぶ。
方針：存在定理から古典的に選択する。
規約：選択された左面は元の列。使われ方：回転後の列の構成。 -/
def chosenCofiberRotationRectangle {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) : CofiberRotationRectangle t :=
  Classical.choice (nonempty_cofiberRotationRectangle t ht)

/-- 概要：回転長方形の外側は入力の始点の suspension 四角形。
方針：外側の左列を元の左列と照合し、二つの零角を確認する。
規約：suspension 頂点は長方形の右上。使われ方：回転後の終点の表示。 -/
def CofiberRotationRectangle.suspensionSquare {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    (r : CofiberRotationRectangle t) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0) where
  square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 1
  zero_corner := by
    have hv : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 1) 0 1 =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 2) 0 1 := rfl
    rw [hv, r.left_eq]
    exact t.zero_corner
  source_eq := by
    have hv : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 1) 0 0 =
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 2) 0 0 := rfl
    rw [hv, r.left_eq]
  other_zero := r.zero_end
  isPushout := r.outer_isPushout

/-- 概要：回転長方形の右面を転置すると回転後の零角の列になる。
方針：右下の零角を転置して零角の標準位置へ移す。
規約：第一射は元の第二射、第二射は右面の上辺。使われ方：回転三角形。 -/
def CofiberRotationRectangle.rotatedZeroTriangle {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    (r : CofiberRotationRectangle t) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X where
  square := (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 0
  zero_corner := by
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 0) 1 0)
    exact r.zero_end

/-- 概要：回転後の零角の列は cofiber 列である。
方針：右面の押し出し性を転置不変性で移す。
規約：値域の quasicategory 性は不要。使われ方：回転三角形の幾何学的な所属。 -/
lemma CofiberRotationRectangle.rotated_isCofiber {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    (r : CofiberRotationRectangle t) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence r.rotatedZeroTriangle :=
  (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).1 r.right_isPushout

/-- 概要：入力の列から外側 suspension への始点固定の比較ホモトピー。
方針：長方形の左から外側への変形の始点を左面の厳密な一致で移す。
規約：時間の向きは元の列から suspension。使われ方：回転後の第二射の照合。 -/
def CofiberRotationRectangle.comparisonHomotopy {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    (r : CofiberRotationRectangle t) : SSet.Homotopy t.square r.suspensionSquare.square where
  h := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy r.diagram).h
  h₀ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy r.diagram).h₀.trans r.left_eq
  h₁ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy r.diagram).h₁
  rel := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy r.diagram).rel

/-- 概要：回転長方形の比較は入力の始点を全時間で固定する。
方針：左面の一致を形状の始点固定条件に代入する。
規約：定値の道の厳密な等号。使われ方：接続射の選択独立性の適用。 -/
lemma CofiberRotationRectangle.comparisonHomotopy_source {X : SSet.{u}} {t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X}
    (r : CofiberRotationRectangle t) :
    ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      r.comparisonHomotopy.h =
        CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy_source r.diagram
  exact h.trans (congrArg (fun R => CartesianMonoidalCategory.snd
    (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0)) r.left_eq)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
