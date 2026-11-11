module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSuspensionParameters
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRowColumnSuspensions
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CurryVertexEvaluation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionDiagrams

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionGridSuspensionFamily_vertex {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X) (i j : Fin 2) :
    (curry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionShape ≫ F)).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ F) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt, Category.assoc] using
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.curry_vertex_evaluation (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionShape ≫ F)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)

def ExcisionSquareGrid.suspension_family {X : SSet.{u}} [Quasicategory X]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid R z)
    (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex
    (curry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionShape ≫ d.extension.full)) (by
      rintro ⟨x, y⟩
      obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
      obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
      rw [excisionGridSuspensionFamily_vertex]
      dsimp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex]
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_functorVertex]
      let Check (T : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) : Prop :=
        _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex T 0 1) ∧ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex T 1 0) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare T
      change Check (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ d.extension.full)
      fin_cases i <;> fin_cases j
      · change Check (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt 0 0 ≫ d.extension.full)
        rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt_source]
        dsimp only [Check]
        simp only [Category.assoc, d.extension.middle_eq, d.extension.core_eq]
        exact ⟨(d.core_suspension hz hR).zero_corner,
          (d.core_suspension hz hR).other_zero, (d.core_suspension hz hR).isPushout⟩
      · change Check (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt 0 1 ≫ d.extension.full)
        rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt_row]
        exact ⟨(d.row_suspension hz).zero_corner,
          (d.row_suspension hz).other_zero, (d.row_suspension hz).isPushout⟩
      · change Check (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt 1 0 ≫ d.extension.full)
        rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt_column]
        dsimp only [Check]
        rw [Category.assoc]
        change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.column_suspension hz).square 1 0) ∧
          _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.column_suspension hz).square 0 1) ∧
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((β_ Δ[1] Δ[1]).hom ≫ (d.column_suspension hz).square)
        exact ⟨(d.column_suspension hz).other_zero, (d.column_suspension hz).zero_corner,
          (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).mp (d.column_suspension hz).isPushout⟩
      · change Check (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt 1 1 ≫ d.extension.full)
        rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt_target]
        exact ⟨(d.final_suspension hz).zero_corner,
          (d.final_suspension hz).other_zero, (d.final_suspension hz).isPushout⟩)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
