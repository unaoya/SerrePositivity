module


public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TrianglePrismLowerSides
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TrianglePrismUpperSides
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square

/-!
概要：辺に制限した元の prism の標準二三角形を、既存の上下三角形と同定する。
方針：二つの標準二単体の退化座標を計算し、元の辺の射の自然性を使う。
規約：両方とも元の同じ二単体。使われ方：右辺の h Fun 分解と指定二三角形の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SquareDiagonal
end SerrePositivity.KST.LocalizingInvariants.SquareDiagonal
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants.SquareDiagonal

lemma upper_coordinates : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 0) =
    ((Δ[1] : SSet.{u}).σ 0 (SSet.yonedaEquiv (𝟙 Δ[1])),
      (Δ[1] : SSet.{u}).σ 1 (SSet.yonedaEquiv (𝟙 Δ[1]))) := by
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

lemma lower_coordinates : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1) =
    ((Δ[1] : SSet.{u}).σ 1 (SSet.yonedaEquiv (𝟙 Δ[1])),
      (Δ[1] : SSet.{u}).σ 0 (SSet.yonedaEquiv (𝟙 Δ[1]))) := by
  apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

variable {A X : SSet.{u}} (k : (Δ[1] : SSet.{u}) ⟶ A) (H : A ⊗ Δ[1] ⟶ X)

lemma upper_restriction : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ (k ▷ Δ[1]) ≫ H) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleUpper H (SSet.yonedaEquiv k) := by
  rw [SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.upper_coordinates]
  exact congrArg (fun v ↦ H.app (Opposite.op ⦋2⦌)
    (v, (Δ[1] : SSet.{u}).σ 1 (SSet.yonedaEquiv (𝟙 Δ[1]))))
      (SSet.σ_naturality_apply k 0 (SSet.yonedaEquiv (𝟙 Δ[1])))

lemma lower_restriction : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (k ▷ Δ[1]) ≫ H) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyEdgeTriangleLower H (SSet.yonedaEquiv k) := by
  rw [SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.lower_coordinates]
  exact congrArg (fun v ↦ H.app (Opposite.op ⦋2⦌)
    (v, (Δ[1] : SSet.{u}).σ 0 (SSet.yonedaEquiv (𝟙 Δ[1]))))
      (SSet.σ_naturality_apply k 1 (SSet.yonedaEquiv (𝟙 Δ[1])))

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
