module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanDiagram
public import SerrePositivity.KST.Fibration.PullbackStrictConstantEdge
public import SerrePositivity.KST.Fibration.TransportSimplexConstantEdge
public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramEdges
public import SerrePositivity.InfinityCategories.F1.Coherent.KanInvertible

/-! # 全 span の同じ coherent Kan 図式による初頂点辺の反転 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x : B.obj _⦋0⦌)

/-- 元の strict Kan 図式の初頂点を保つ射の像は、同じ fiber 内の prism により実際の同値。 -/
theorem weakSpanKanDiagram_map_initial_isQCatEquivalence
    {c d : TransportSimplexCategory B.obj} (f : c ⟶ d) (hf : TransportSimplexPreservesFirst f) :
    IsQCatEquivalence ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanDiagram i x).map f) := by
  have : CocartesianFibration (pullback.snd
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x)
      (transportSimplexFirstVertexMap B.obj)) :=
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection_cocartesianFibration i x
  exact cocartesianKanDiagram_map_constantEdge_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x)
    (transportSimplexFirstVertexMap B.obj) f _ rfl
    (transportSimplexFirstVertexMap_target_of_preservesFirst f hf)
    (_root_.SerrePositivity.InfinityCategories.Stable.Transport.transportSimplexFirstVertexMap_interval_constant f hf)

/-- 元の全単体上の空間値図式そのものが、持ち上げた全初頂点辺を反転する。 -/
theorem weakSpanKanCoherentDiagram_inverts_initial :
    InvertsEdges (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanCoherentDiagram i x) (transportSimplexInitialEdgesLifted B.obj) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨c, d, f, hf, rfl⟩ := ht
  apply (isInvertibleEdge_congr (show
    ((edgeOfSimplex (ULift.up (nerve.edgeMk f).edge)).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanCoherentDiagram i x))).edge =
        (coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanDiagram i x).map f)).edge from
          kanDiagramCoherentNerve_edge (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanDiagram i x) f)).mpr
  exact coherentKanEdge_isInvertible_of_isQCatEquivalence
    (weakSpanKanDiagram_map_initial_isQCatEquivalence i x f hf)

end SerrePositivity.KST.Fibration
