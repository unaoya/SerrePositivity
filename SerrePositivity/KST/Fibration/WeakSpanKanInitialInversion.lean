module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakSpanKanDiagram
public import SerrePositivity.KST.Fibration.PullbackStrictConstantEdge
public import SerrePositivity.KST.Fibration.TransportSimplexConstantEdge
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible

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
variable {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (x : B.obj _⦋0⦌)

/-- 元の strict Kan 図式の初頂点を保つ射の像は、同じ fiber 内の prism により実際の同値。 -/
theorem weakSpanKanDiagram_map_initial_isQCatEquivalence
    {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B.obj} (f : c ⟶ d) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexPreservesFirst f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x).map f) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (pullback.snd
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexProjection_cocartesianFibration i x
  exact cocartesianKanDiagram_map_constantEdge_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj) f _ rfl
    (transportSimplexFirstVertexMap_target_of_preservesFirst f hf)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.transportSimplexFirstVertexMap_interval_constant f hf)

/-- 元の全単体上の空間値図式そのものが、持ち上げた全初頂点辺を反転する。 -/
theorem weakSpanKanCoherentDiagram_inverts_initial :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanCoherentDiagram i x) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdgesLifted B.obj) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨c, d, f, hf, rfl⟩ := ht
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ULift.up (nerve.edgeMk f).edge)).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanCoherentDiagram i x))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x).map f)).edge from
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_edge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x) f)).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
    (weakSpanKanDiagram_map_initial_isQCatEquivalence i x f hf)

end SerrePositivity.KST.Fibration
