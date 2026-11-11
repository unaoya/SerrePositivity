module
public import SerrePositivity.KST.Fibration.LeftFibrationInvertedBaseChange
public import SerrePositivity.KST.Fibration.PullbackStrictBilateralEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakSpanKanWeakInversion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.FractionKanDescent
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexEdgeCover
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.InvertingFunctorIsoInvariance
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LocalizationSourceIso

/-! # 商の元の coslice 空間値図式による、同じ W 分母の反転 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)
include h

/-- 商の coslice の同じ strict Kan 図式は、W 上の元の射を実際の同値へ送る。 -/
theorem fractionSimplexKanMappingDiagram_map_weak_isQCatEquivalence
    {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B.obj} (f : c ⟶ d)
    (hf : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk f).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x).map f) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj
  let b := yonedaEquiv.symm (nerve.edgeMk f).edge ≫ k
  have hW : ∀ e : (Δ[1] : SSet.{u}) _⦋1⦌,
      b.app (Opposite.op ⦋1⦌) e ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
    intro e
    have hb : b = yonedaEquiv.symm (k.app (Opposite.op ⦋1⦌) (nerve.edgeMk f).edge) :=
      yonedaEquiv_symm_comp _ _
    rw [hb]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakDenominatorInterval_edges_mem h _ hf e
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (b ≫ q.hom) Set.univ := by
    intro e _
    have hi := h.inverts (hW e)
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (b.app (Opposite.op ⦋1⦌) e)).map
      ((truncation 2).map q.hom)) (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map
        ((truncation 2).map (b ≫ q.hom))) rfl).mp
    exact hi
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (pullback.snd p
      (yonedaEquiv.symm (nerve.edgeMk f).edge ≫ (k ≫ q.hom))) := by
    exact leftFibrationBaseChange_cartesian_of_inverts p
      (yonedaEquiv.symm (nerve.edgeMk f).edge ≫ (k ≫ q.hom))
      (by simpa only [b, Category.assoc] using hb)
  exact cocartesianKanDiagram_map_bilateralEdge_isQCatEquivalence p (k ≫ q.hom) f

/-- 同じ coherent coslice 図式自身は、持ち上げた W の全逆像を反転する。 -/
theorem fractionSimplexKanMappingDiagram_inverts_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x))
      (ULift.up '' _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanTransportEdges i) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨c, d, f, rfl⟩ := ComposableArrows.mk₁_surjective t
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ULift.up (nerve.edgeMk f).edge)).map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x)))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x).map f)).edge from
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_edge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x) f)).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
    (fractionSimplexKanMappingDiagram_map_weak_isQCatEquivalence h x f ht)

/-- 元の底へ降下した同じ coslice 空間値図式も、元の W 辺を全て反転する。 -/
theorem fractionKanSpaceDiagram_inverts_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram q.hom x) (ULift.up '' _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) := by
  have hp := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram_restrictionIso q.hom x).invertsEdges_iff
    (ULift.up '' _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanTransportEdges i)).mpr
      (fractionSimplexKanMappingDiagram_inverts_weak h x)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.invertsEdges_precomp_iff_of_image
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj))
    (ULift.up '' _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanTransportEdges i) (ULift.up '' _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_ulift_edge_image B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionKanSpaceDiagram q.hom x)).mp hp

end SerrePositivity.KST.Fibration
