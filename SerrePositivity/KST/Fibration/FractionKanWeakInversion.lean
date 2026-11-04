module
public import SerrePositivity.KST.Fibration.LeftFibrationInvertedBaseChange
public import SerrePositivity.KST.Fibration.PullbackStrictBilateralEdge
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanWeakInversion
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionKanDescent
public import SerrePositivity.KST.Fibration.TransportSimplexEdgeCover
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.InvertingFunctorIsoInvariance
public import SerrePositivity.InfinityCategories.F1.Diagrams.LocalizationSourceIso

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
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)
include h

/-- 商の coslice の同じ strict Kan 図式は、W 上の元の射を実際の同値へ送る。 -/
theorem fractionSimplexKanMappingDiagram_map_weak_isQCatEquivalence
    {c d : TransportSimplexCategory B.obj} (f : c ⟶ d)
    (hf : (transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk f).edge ∈ weakEquivalences i) :
    IsQCatEquivalence ((fractionSimplexKanMappingDiagram q.hom x).map f) := by
  let p := sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))
  let k := transportSimplexFirstVertexMap B.obj
  let b := yonedaEquiv.symm (nerve.edgeMk f).edge ≫ k
  have hW : ∀ e : (Δ[1] : SSet.{u}) _⦋1⦌,
      b.app (Opposite.op ⦋1⦌) e ∈ weakEquivalences i := by
    intro e
    have hb : b = yonedaEquiv.symm (k.app (Opposite.op ⦋1⦌) (nerve.edgeMk f).edge) :=
      yonedaEquiv_symm_comp _ _
    rw [hb]
    exact weakDenominatorInterval_edges_mem h _ hf e
  have hb : InvertsEdges (b ≫ q.hom) Set.univ := by
    intro e _
    have hi := h.inverts (hW e)
    apply (isInvertibleEdge_congr (e := (edgeOfSimplex (b.app (Opposite.op ⦋1⦌) e)).map
      ((truncation 2).map q.hom)) (f := (edgeOfSimplex e).map
        ((truncation 2).map (b ≫ q.hom))) rfl).mp
    exact hi
  have hc : CartesianFibration (pullback.snd p
      (yonedaEquiv.symm (nerve.edgeMk f).edge ≫ (k ≫ q.hom))) := by
    exact leftFibrationBaseChange_cartesian_of_inverts p
      (yonedaEquiv.symm (nerve.edgeMk f).edge ≫ (k ≫ q.hom))
      (by simpa only [b, Category.assoc] using hb)
  exact cocartesianKanDiagram_map_bilateralEdge_isQCatEquivalence p (k ≫ q.hom) f

/-- 同じ coherent coslice 図式自身は、持ち上げた W の全逆像を反転する。 -/
theorem fractionSimplexKanMappingDiagram_inverts_weak :
    InvertsEdges (kanDiagramCoherentNerve (fractionSimplexKanMappingDiagram q.hom x))
      (ULift.up '' weakSpanTransportEdges i) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨c, d, f, rfl⟩ := ComposableArrows.mk₁_surjective t
  apply (isInvertibleEdge_congr (show
    ((edgeOfSimplex (ULift.up (nerve.edgeMk f).edge)).map ((truncation 2).map
      (kanDiagramCoherentNerve (fractionSimplexKanMappingDiagram q.hom x)))).edge =
        (coherentNerveEdge ((fractionSimplexKanMappingDiagram q.hom x).map f)).edge from
          kanDiagramCoherentNerve_edge (fractionSimplexKanMappingDiagram q.hom x) f)).mpr
  exact coherentKanEdge_isInvertible_of_isQCatEquivalence
    (fractionSimplexKanMappingDiagram_map_weak_isQCatEquivalence h x f ht)

/-- 元の底へ降下した同じ coslice 空間値図式も、元の W 辺を全て反転する。 -/
theorem fractionKanSpaceDiagram_inverts_weak :
    InvertsEdges (fractionKanSpaceDiagram q.hom x) (ULift.up '' weakEquivalences i) := by
  have hp := ((fractionKanSpaceDiagram_restrictionIso q.hom x).invertsEdges_iff
    (ULift.up '' weakSpanTransportEdges i)).mpr
      (fractionSimplexKanMappingDiagram_inverts_weak h x)
  exact (invertsEdges_precomp_iff_of_image
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj))
    (ULift.up '' weakSpanTransportEdges i) (ULift.up '' weakEquivalences i)
    (transportSimplexFirstVertexMap_ulift_edge_image B.obj (weakEquivalences i))
    (fractionKanSpaceDiagram q.hom x)).mp hp

end SerrePositivity.KST.Fibration
