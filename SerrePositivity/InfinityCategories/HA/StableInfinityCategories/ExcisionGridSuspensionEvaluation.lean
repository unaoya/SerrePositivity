module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSuspensionFamily

/-!
概要：実 suspension 全単体族の始点評価と終点評価を元の二四角形と同定する。
方針：同じ実図式の貼り合わせ・全パラメーターの評価・普遍的な切断比較を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionGridSuspensionEvaluateShape (a b : Fin 2) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} :=
  lift (SSet.const (stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b))
    (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionShape

lemma excisionGridSuspensionEvaluateShape_source :
    excisionGridSuspensionEvaluateShape.{u} 0 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridSuspensionEvaluateShape_target :
    excisionGridSuspensionEvaluateShape.{u} 1 1 =
      (β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridFinalSquare := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma ExcisionSquareGrid.suspension_family_source {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid R z)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R) :
    d.suspension_family hz hR ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0 = R := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid.suspension_family, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.curry_evaluation_vertex]
  change excisionGridSuspensionEvaluateShape 0 0 ≫ d.extension.full = R
  rw [excisionGridSuspensionEvaluateShape_source]
  exact d.square_restriction

lemma ExcisionSquareGrid.suspension_family_target {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid R z)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R) :
    d.suspension_family hz hR ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1 =
      (β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridFinalSquare ≫ d.extension.full := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid.suspension_family, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.curry_evaluation_vertex]
  change excisionGridSuspensionEvaluateShape 1 1 ≫ d.extension.full = _
  rw [excisionGridSuspensionEvaluateShape_target, Category.assoc]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
