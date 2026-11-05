module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanDescent
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanWeakInversion
public import SerrePositivity.InfinityCategories.F1.Transport.TransportSimplexEdgeCover
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.InvertingFunctorIsoInvariance
public import SerrePositivity.InfinityCategories.F1.Diagrams.LocalizationSourceIso

/-! # 元の底へ降下した同じ空間値分数図式による W の反転 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}

/-- 元の降下図式自身が、宇宙を揃えた W の全辺を反転する。
全関手圏内の制限同型と全辺の厳密な被覆で反映し、各値の同値だけには頼らない。 -/
theorem weakSpanKanSpaceDiagram_inverts_weak (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    InvertsEdges (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanSpaceDiagram i x) (ULift.up '' _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) := by
  have hp : InvertsEdges
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj) ≫
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanSpaceDiagram i x) (ULift.up '' _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanTransportEdges i) :=
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanSpaceDiagram_restrictionIso i x).invertsEdges_iff _).mpr
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanCoherentDiagram_inverts_weak h x)
  exact (invertsEdges_precomp_iff_of_image
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj))
    (ULift.up '' _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanTransportEdges i) (ULift.up '' _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i)
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportSimplexFirstVertexMap_ulift_edge_image B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i))
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanSpaceDiagram i x)).mp hp

end SerrePositivity.KST.Fibration
