module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSuspensionFamily

/-!
概要：四つの実 suspension 面の引き戻し性から、元の押し出しの像の普遍性を導く。
方針：全 cospan の厳密保存、同じ θ と対角合成、元の入力面の極限錐を接続する。
規約：標的の零対象や一般安定性は仮定しない。使われ方：一般切除・loop 同値判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma ExcisionSquareGrid.suspension_at_isSuspension {C : SSet.{u}} [Quasicategory C]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C} {z : C _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid R z) (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ d.extension.full) 0 1) ∧
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ d.extension.full) 1 0) ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt i j ≫ d.extension.full) := by
  have h := ((d.suspension_family hz hR).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)).property (𝟙 ⦋0⦌)
  simp only [op_id, CategoryTheory.Functor.map_id_apply] at h
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex
    ((curry (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionShape ≫ d.extension.full)).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)) at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionFamily_vertex] at h
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex] at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_functorVertex] at h
  exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
