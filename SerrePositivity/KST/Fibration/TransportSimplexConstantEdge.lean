module
public import SerrePositivity.KST.Fibration.StrictTransportUnderEdge
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexLocalizationData

/-! # 初頂点を保つ射の元の底での定値区間と両端 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 初頂点を保つ射の区間は、元の底の同じ初頂点に厳密に定値。 -/
theorem transportSimplexFirstVertexMap_interval_constant {B : SSet.{u}}
    {c d : TransportSimplexCategory B} (f : c ⟶ d) (hf : TransportSimplexPreservesFirst f) :
    yonedaEquiv.symm (nerve.edgeMk f).edge ≫ transportSimplexFirstVertexMap B =
      SSet.const ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c)) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  refine (transportSimplexFirstVertexMap_edge_of_preservesFirst f hf).trans ?_
  change B.σ 0 _ = PinchedHom.constant _ 1
  exact (pinchedConstant_one _).symm

/-- 同じ元の射の終点の初頂点も、始点の初頂点そのもの。 -/
theorem transportSimplexFirstVertexMap_target_of_preservesFirst {B : SSet.{u}}
    {c d : TransportSimplexCategory B} (f : c ⟶ d) (hf : TransportSimplexPreservesFirst f) :
    (transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex d) =
      (transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c) := by
  have ht : (yonedaEquiv.symm (nerve.edgeMk f).edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = nerveVertex d := by
    rw [← intervalMap_target, Equiv.apply_symm_apply]
    exact ComposableArrows.ext₀ rfl
  have he := congrArg (fun m : (Δ[1] : SSet.{u}) ⟶ B =>
    m.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (transportSimplexFirstVertexMap_interval_constant f hf)
  have he' : (transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
      ((yonedaEquiv.symm (nerve.edgeMk f).edge).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
      PinchedHom.constant
        ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c)) 0 := he
  exact (congrArg ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)) ht).symm.trans
    (he'.trans (pinchedConstant_zero _))

end SerrePositivity.KST.Fibration
