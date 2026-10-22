module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridSuspensionFamily

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
namespace SerrePositivity.InfinityCategories

def excisionGridSuspensionEvaluateShape (a b : Fin 2) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ nerve ExcisionGridIndex.{u} :=
  lift (SSet.const (stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b))
    (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) ≫ excisionGridSuspensionShape

lemma excisionGridSuspensionEvaluateShape_source :
    excisionGridSuspensionEvaluateShape.{u} 0 0 = excisionGridSquareEmbedding := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridSuspensionEvaluateShape_target :
    excisionGridSuspensionEvaluateShape.{u} 1 1 =
      (β_ Δ[1] Δ[1]).hom ≫ excisionGridFinalSquare := by
  apply thinNerveHom_ext_of_vertices
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  fin_cases i <;> fin_cases j <;> apply ULift.ext <;> apply Subtype.ext <;>
    apply Prod.ext <;> apply Fin.ext <;> decide

lemma ExcisionSquareGrid.suspension_family_source {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z)
    (hz : IsZeroVertex z) (hR : IsPushoutSquare R) :
    d.suspension_family hz hR ≫ suspensionDiagramEvaluation X 0 0 = R := by
  dsimp only [ExcisionSquareGrid.suspension_family, suspensionDiagramEvaluation]
  rw [← Category.assoc, fullSubcomplexLift_ι, curry_evaluation_vertex]
  change excisionGridSuspensionEvaluateShape 0 0 ≫ d.extension.full = R
  rw [excisionGridSuspensionEvaluateShape_source]
  exact d.square_restriction

lemma ExcisionSquareGrid.suspension_family_target {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z)
    (hz : IsZeroVertex z) (hR : IsPushoutSquare R) :
    d.suspension_family hz hR ≫ suspensionDiagramEvaluation X 1 1 =
      (β_ Δ[1] Δ[1]).hom ≫ excisionGridFinalSquare ≫ d.extension.full := by
  dsimp only [ExcisionSquareGrid.suspension_family, suspensionDiagramEvaluation]
  rw [← Category.assoc, fullSubcomplexLift_ι, curry_evaluation_vertex]
  change excisionGridSuspensionEvaluateShape 1 1 ≫ d.extension.full = _
  rw [excisionGridSuspensionEvaluateShape_target, Category.assoc]

end SerrePositivity.InfinityCategories
