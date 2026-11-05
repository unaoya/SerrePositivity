module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.KST.Fibration.WeakSpanKanInitialInversion
public import SerrePositivity.KST.Fibration.PullbackStrictBilateralEdge
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakDenominatorSpanTransport

/-! # 元の W 辺の上にある射を同じ coherent 分数図式が反転する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}

/-- 初頂点写像で W 辺へ写る射は、元の全 strict section の Kan 図式で同値になる。 -/
theorem weakSpanKanDiagram_map_weak_isQCatEquivalence (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) {c d : TransportSimplexCategory B.obj} (f : c ⟶ d)
    (hf : (transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk f).edge ∈ weakEquivalences i) :
    IsQCatEquivalence ((weakSpanKanDiagram i x).map f) := by
  let π := markedSpanFamilyProjection B.obj (weakEquivalences i) x
  let k := transportSimplexFirstVertexMap B.obj
  let b := yonedaEquiv.symm (nerve.edgeMk f).edge ≫ k
  have hW : ∀ e : (Δ[1] : SSet.{u}) _⦋1⦌,
      b.app (Opposite.op ⦋1⦌) e ∈ weakEquivalences i := by
    intro e
    have hb : b = yonedaEquiv.symm (k.app (Opposite.op ⦋1⦌) (nerve.edgeMk f).edge) :=
      yonedaEquiv_symm_comp _ _
    rw [hb]
    exact weakDenominatorInterval_edges_mem h _ hf e
  have : CartesianFibration (pullback.snd π b) :=
    weakSpanDenominatorBaseChange_cartesianFibration h x b hW
  have : CocartesianFibration (pullback.snd π b) :=
    weakSpanBaseChange_cocartesianFibration (i := i) x b
  have : CocartesianFibration (pullback.snd π k) :=
    weakSpanBaseChange_cocartesianFibration (i := i) x k
  exact cocartesianKanDiagram_map_bilateralEdge_isQCatEquivalence π k f

/-- W の全逆像を指定辺とする。全単体は同じ初頂点写像によって判定する。 -/
def weakSpanTransportEdges (i : ExactMap A B) :
    Set ((nerve (TransportSimplexCategory B.obj)) _⦋1⦌) :=
  (transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋1⦌) ⁻¹' weakEquivalences i

/-- 元の coherent 分数図式そのものは、持ち上げた W の全逆像を反転する。 -/
theorem weakSpanKanCoherentDiagram_inverts_weak (h : IsVerdierSequence i q)
    (x : B.obj _⦋0⦌) :
    InvertsEdges (weakSpanKanCoherentDiagram i x) (ULift.up '' weakSpanTransportEdges i) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨c, d, f, rfl⟩ := ComposableArrows.mk₁_surjective t
  apply (isInvertibleEdge_congr (show
    ((edgeOfSimplex (ULift.up (nerve.edgeMk f).edge)).map
      ((truncation 2).map (weakSpanKanCoherentDiagram i x))).edge =
        (coherentNerveEdge ((weakSpanKanDiagram i x).map f)).edge from
          kanDiagramCoherentNerve_edge (weakSpanKanDiagram i x) f)).mpr
  exact coherentKanEdge_isInvertible_of_isQCatEquivalence
    (weakSpanKanDiagram_map_weak_isQCatEquivalence h x f ht)

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanCoherentDiagram_inverts_weak := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanCoherentDiagram_inverts_weak

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanDiagram_map_weak_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanDiagram_map_weak_isQCatEquivalence

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanTransportEdges (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanTransportEdges := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanTransportEdges
