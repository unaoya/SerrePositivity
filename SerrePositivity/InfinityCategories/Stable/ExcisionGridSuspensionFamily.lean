module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridSuspensionParameters
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridRowColumnSuspensions
public import SerrePositivity.InfinityCategories.Stable.CurryVertexEvaluation
public import SerrePositivity.InfinityCategories.Stable.SuspensionDiagrams

/-!
概要：元の押し出し四角形上の実 suspension 図式の全単体族。
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

lemma excisionGridSuspensionFamily_vertex {X : SSet.{u}}
    (F : nerve ExcisionGridIndex.{u} ⟶ X) (i j : Fin 2) :
    (curry (excisionGridSuspensionShape ≫ F)).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) =
      functorVertex (excisionGridSuspensionAt i j ≫ F) := by
  simpa only [excisionGridSuspensionAt, Category.assoc] using
    curry_vertex_evaluation (excisionGridSuspensionShape ≫ F)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)

def ExcisionSquareGrid.suspension_family {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : ExcisionSquareGrid R z)
    (hz : IsZeroVertex z) (hR : IsPushoutSquare R) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ suspensionDiagrams X :=
  fullSubcomplexLift IsSuspensionDiagramVertex
    (curry (excisionGridSuspensionShape ≫ d.extension.full)) (by
      rintro ⟨x, y⟩
      obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
      obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
      rw [excisionGridSuspensionFamily_vertex]
      dsimp only [IsSuspensionDiagramVertex]
      rw [squareDiagram_functorVertex]
      let Check (T : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) : Prop :=
        IsZeroVertex (squareVertex T 0 1) ∧ IsZeroVertex (squareVertex T 1 0) ∧ IsPushoutSquare T
      change Check (excisionGridSuspensionAt i j ≫ d.extension.full)
      fin_cases i <;> fin_cases j
      · change Check (excisionGridSuspensionAt 0 0 ≫ d.extension.full)
        rw [excisionGridSuspensionAt_source]
        dsimp only [Check]
        simp only [Category.assoc, d.extension.middle_eq, d.extension.core_eq]
        exact ⟨(d.core_suspension hz hR).zero_corner,
          (d.core_suspension hz hR).other_zero, (d.core_suspension hz hR).isPushout⟩
      · change Check (excisionGridSuspensionAt 0 1 ≫ d.extension.full)
        rw [excisionGridSuspensionAt_row]
        exact ⟨(d.row_suspension hz).zero_corner,
          (d.row_suspension hz).other_zero, (d.row_suspension hz).isPushout⟩
      · change Check (excisionGridSuspensionAt 1 0 ≫ d.extension.full)
        rw [excisionGridSuspensionAt_column]
        dsimp only [Check]
        rw [Category.assoc]
        change IsZeroVertex (squareVertex (d.column_suspension hz).square 1 0) ∧
          IsZeroVertex (squareVertex (d.column_suspension hz).square 0 1) ∧
          IsPushoutSquare ((β_ Δ[1] Δ[1]).hom ≫ (d.column_suspension hz).square)
        exact ⟨(d.column_suspension hz).other_zero, (d.column_suspension hz).zero_corner,
          (isPushoutSquare_iff_transpose _).mp (d.column_suspension hz).isPushout⟩
      · change Check (excisionGridSuspensionAt 1 1 ≫ d.extension.full)
        rw [excisionGridSuspensionAt_target]
        exact ⟨(d.final_suspension hz).zero_corner,
          (d.final_suspension hz).other_zero, (d.final_suspension hz).isPushout⟩)

end SerrePositivity.InfinityCategories
