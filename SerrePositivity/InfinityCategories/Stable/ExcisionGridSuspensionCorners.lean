module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridSuspensionFamily

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
namespace SerrePositivity.InfinityCategories

lemma ExcisionSquareGrid.suspension_at_isSuspension {C : SSet.{u}} [Quasicategory C]
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C} {z : C _⦋0⦌}
    (d : ExcisionSquareGrid R z) (hz : IsZeroVertex z) (hR : IsPushoutSquare R)
    (i j : Fin 2) :
    IsZeroVertex (squareVertex (excisionGridSuspensionAt i j ≫ d.extension.full) 0 1) ∧
    IsZeroVertex (squareVertex (excisionGridSuspensionAt i j ≫ d.extension.full) 1 0) ∧
    IsPushoutSquare (excisionGridSuspensionAt i j ≫ d.extension.full) := by
  have h := ((d.suspension_family hz hR).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)).property (𝟙 ⦋0⦌)
  simp only [op_id, CategoryTheory.Functor.map_id_apply] at h
  change IsSuspensionDiagramVertex
    ((curry (excisionGridSuspensionShape ≫ d.extension.full)).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)) at h
  rw [excisionGridSuspensionFamily_vertex] at h
  dsimp only [IsSuspensionDiagramVertex] at h
  rw [squareDiagram_functorVertex] at h
  exact h

end SerrePositivity.InfinityCategories
