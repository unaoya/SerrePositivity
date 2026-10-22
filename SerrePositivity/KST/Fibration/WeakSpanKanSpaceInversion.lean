module
public import SerrePositivity.KST.Fibration.WeakSpanKanDescent
public import SerrePositivity.KST.Fibration.WeakSpanKanWeakInversion
public import SerrePositivity.KST.Fibration.TransportSimplexEdgeCover
public import SerrePositivity.InfinityCategories.F1.InvertingFunctorIsoInvariance
public import SerrePositivity.InfinityCategories.F1.LocalizationSourceIso

/-! # 元の底へ降下した同じ空間値分数図式による W の反転 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}

/-- 元の降下図式自身が、宇宙を揃えた W の全辺を反転する。
全関手圏内の制限同型と全辺の厳密な被覆で反映し、各値の同値だけには頼らない。 -/
theorem weakSpanKanSpaceDiagram_inverts_weak (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    InvertsEdges (weakSpanKanSpaceDiagram i x) (ULift.up '' weakEquivalences i) := by
  have hp : InvertsEdges
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj) ≫
        weakSpanKanSpaceDiagram i x) (ULift.up '' weakSpanTransportEdges i) :=
    ((weakSpanKanSpaceDiagram_restrictionIso i x).invertsEdges_iff _).mpr
      (weakSpanKanCoherentDiagram_inverts_weak h x)
  exact (invertsEdges_precomp_iff_of_image
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj))
    (ULift.up '' weakSpanTransportEdges i) (ULift.up '' weakEquivalences i)
    (transportSimplexFirstVertexMap_ulift_edge_image B.obj (weakEquivalences i))
    (weakSpanKanSpaceDiagram i x)).mp hp

end SerrePositivity.KST.Fibration
