module
public import SerrePositivity.KST.Fibration.FractionSimplexKanComparison
public import SerrePositivity.KST.Fibration.PullbackStrictConstantEdge
public import SerrePositivity.KST.Fibration.TransportSimplexConstantEdge
public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramEdges

/-! # 商の coslice の同じ strict Kan 図式による初頂点辺の反転 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (x : X _⦋0⦌)

/-- 同じ商像の coslice 図式は、元の初頂点を保つ射を同値へ送る。 -/
theorem fractionSimplexKanMappingDiagram_map_initial_isQCatEquivalence
    {c d : TransportSimplexCategory X} (f : c ⟶ d) (hf : TransportSimplexPreservesFirst f) :
    IsQCatEquivalence ((fractionSimplexKanMappingDiagram F x).map f) := by
  have hb : yonedaEquiv.symm (nerve.edgeMk f).edge ≫
      (transportSimplexFirstVertexMap X ≫ F) =
      SSet.const (F.app (Opposite.op ⦋0⦌)
        ((transportSimplexFirstVertexMap X).app (Opposite.op ⦋0⦌) (nerveVertex c))) := by
    rw [← Category.assoc, transportSimplexFirstVertexMap_interval_constant f hf, SSet.const_comp]
  exact cocartesianKanDiagram_map_constantEdge_isQCatEquivalence
    (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
    (transportSimplexFirstVertexMap X ≫ F) f _ rfl
    (congrArg (F.app (Opposite.op ⦋0⦌))
      (transportSimplexFirstVertexMap_target_of_preservesFirst f hf)) hb

/-- 元の全 coherent coslice 図式自身が、持ち上げた初頂点辺を反転する。 -/
theorem fractionSimplexKanMappingDiagram_inverts_initial :
    InvertsEdges (kanDiagramCoherentNerve (fractionSimplexKanMappingDiagram F x))
      (transportSimplexInitialEdgesLifted X) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨c, d, f, hf, rfl⟩ := ht
  apply (isInvertibleEdge_congr (show
    ((edgeOfSimplex (ULift.up (nerve.edgeMk f).edge)).map
      ((truncation 2).map (kanDiagramCoherentNerve (fractionSimplexKanMappingDiagram F x)))).edge =
        (coherentNerveEdge ((fractionSimplexKanMappingDiagram F x).map f)).edge from
          kanDiagramCoherentNerve_edge (fractionSimplexKanMappingDiagram F x) f)).mpr
  exact coherentKanEdge_isInvertible_of_isQCatEquivalence
    (fractionSimplexKanMappingDiagram_map_initial_isQCatEquivalence F x f hf)

end SerrePositivity.KST.Fibration
