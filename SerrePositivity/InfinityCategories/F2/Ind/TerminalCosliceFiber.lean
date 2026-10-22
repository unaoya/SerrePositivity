module

public import SerrePositivity.InfinityCategories.F2.Ind.TerminalCosliceBoundary
public import SerrePositivity.InfinityCategories.Core.VertexFiber

/-!
概要：点から同じ終対象への coslice の fiber は可縮な Kan 複体。
方針：元の境界を定値単体の上で延長し、同じ fiber へ戻す。
規約：周囲の単体集合や coslice の quasicategory 性は不要。
使われ方：cofinal 性の証明で、指定した終頂点への枝の選択を充填する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ終頂点上の元の coslice fiber の全境界は充填できる。 -/
lemma pointCoslice_terminalFiber_isContractibleKan {X : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ X) {x : X _⦋0⦌} (hx : IsTerminalVertex x) :
    IsContractibleKan (vertexFiber (sliceUnderProjection p) x) := by
  intro n a
  have h : (a ≫ vertexFiberι (sliceUnderProjection p) x) ≫ sliceUnderProjection p =
      (boundary n).ι ≫ SSet.const x := by
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  have ht : IsTerminalVertex
      ((SSet.const x : (Δ[n] : SSet.{u}) ⟶ X).app _ (stdSimplex.obj₀Equiv.symm (Fin.last n))) := by
    change IsTerminalVertex (X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op x)
    rw [SimplexCategory.hom_zero_zero (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0)]
    change IsTerminalVertex (X.map (𝟙 _) x)
    rw [CategoryTheory.Functor.map_id_apply]
    exact hx
  obtain ⟨F, hF, hproj⟩ := exists_pointCosliceBoundary_lift_over_terminal p n
    (a ≫ vertexFiberι (sliceUnderProjection p) x) (SSet.const x) h ht
  refine ⟨vertexFiberLift (sliceUnderProjection p) x F hproj, ?_⟩
  apply vertexFiber_hom_ext (sliceUnderProjection p) x
  rw [Category.assoc, vertexFiberLift_ι]
  exact hF

end SerrePositivity.InfinityCategories.F2.Ind
