module
public import SerrePositivity.KST.Fibration.IdentityMarkedSpan
public import SerrePositivity.KST.Fibration.WeakSpanKanDiagram
public import SerrePositivity.KST.Fibration.WeakDenominatorSpanTransport
public import SerrePositivity.InfinityCategories.F1.TransportSimplexFirstVertexNaturality

/-! # 元の恒等 span を、同じ strict section と Kan 分数図式の実際の点へ移す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

include h in
/-- 元の恒等辺は、同じ商関手が反転する W 分母。 -/
theorem weakIdentitySpan_mem : PinchedHom.constant x 1 ∈ weakEquivalences i := by
  rw [weakEquivalences_eq_invertedEdges h]
  exact invertedEdges_constant q.hom x

/-- 元の両端固定分数空間の恒等点。 -/
def weakIdentityFixedSpan : (fixedMarkedSpans B.obj (weakEquivalences i) x x) _⦋0⦌ :=
  identityFixedMarkedSpan (weakEquivalences i) x (weakIdentitySpan_mem h x)

/-- 零単体を添字とする初頂点は、元の同じ頂点そのもの。 -/
theorem transportSimplexFirstVertexMap_zeroIndex {X : SSet.{u}} (x : X _⦋0⦌) :
    (transportSimplexFirstVertexMap X).app (Opposite.op ⦋0⦌)
      (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x)) = x := by
  rw [transportSimplexFirstVertexMap_vertex]
  have he : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply SSet.stdSimplex.ext
    intro k
    apply Fin.ext
    omega
  rw [he, yonedaEquiv_symm_app_id]

/-- 恒等 span を、全単体圏上の同じ厳密 fiber 同型で運んだ点。 -/
def weakIdentitySimplexFiberPoint :
    (vertexFiber (weakSpanSimplexProjection i x)
      (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x))) _⦋0⦌ :=
  (weakSpanSimplexFiberIso i x (transportSimplexIndex (n := ⦋0⦌) x)).hom.app
    (Opposite.op ⦋0⦌)
      ((eqToHom (congrArg (fun y => fixedMarkedSpans B.obj (weakEquivalences i) x y)
        (transportSimplexFirstVertexMap_zeroIndex x).symm)).app (Opposite.op ⦋0⦌)
          (weakIdentityFixedSpan h x))

/-- 同じ恒等射評価の自明 Kan fibration の切断を選ぶ。 -/
def weakIdentityStrictEvaluationSection :
    vertexFiber (weakSpanSimplexProjection i x)
        (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x)) ⟶
      kanCocartesianStrictTransport (weakSpanSimplexProjection i x)
        (transportSimplexIndex (n := ⦋0⦌) x) :=
  Classical.choose (trivialKanFibration_exists_section
    (kanCocartesianStrictTransportEvaluate (weakSpanSimplexProjection i x)
      (transportSimplexIndex (n := ⦋0⦌) x)))

/-- 元の恒等 span を厳密に評価値とする、全 cocartesian section の実際の点。 -/
def weakIdentityStrictSectionPoint :
    (kanCocartesianStrictTransport (weakSpanSimplexProjection i x)
      (transportSimplexIndex (n := ⦋0⦌) x)) _⦋0⦌ :=
  (weakIdentityStrictEvaluationSection (i := i) x).app (Opposite.op ⦋0⦌)
    (weakIdentitySimplexFiberPoint h x)

/-- 評価は、構成に用いた同じ恒等 span の fiber 点を厳密に回収する。 -/
theorem weakIdentityStrictSectionPoint_evaluate :
    (kanCocartesianStrictTransportEvaluate (weakSpanSimplexProjection i x)
      (transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
        (weakIdentityStrictSectionPoint h x) = weakIdentitySimplexFiberPoint h x :=
  congrArg (fun m => m.app (Opposite.op ⦋0⦌) (weakIdentitySimplexFiberPoint h x))
    (Classical.choose_spec (trivialKanFibration_exists_section
      (kanCocartesianStrictTransportEvaluate (weakSpanSimplexProjection i x)
        (transportSimplexIndex (n := ⦋0⦌) x))))

/-- 同じ strict Kan 分数図式の値における、元の恒等 span からの指定点。 -/
def weakIdentityKanPoint :
    (((weakSpanKanDiagram i x).obj (transportSimplexIndex (n := ⦋0⦌) x)).obj) _⦋0⦌ :=
  (F2.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
    (weakIdentityStrictSectionPoint h x)

/-- Kan 置換後の同じ評価も、元の恒等 span の fiber 点の単位像を厳密に回収する。 -/
theorem weakIdentityKanPoint_evaluate :
    (cocartesianKanDiagramFiberComparison (weakSpanSimplexProjection i x)
      (transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
        (weakIdentityKanPoint h x) =
      (F2.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
        (weakIdentitySimplexFiberPoint h x) := by
  have hn := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (weakIdentityStrictSectionPoint h x))
    (F2.continuousKanReplacementUnit.naturality
      (kanCocartesianStrictTransportEvaluate (weakSpanSimplexProjection i x)
        (transportSimplexIndex (n := ⦋0⦌) x)))
  exact hn.symm.trans (congrArg
    ((F2.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌))
    (weakIdentityStrictSectionPoint_evaluate h x))

end SerrePositivity.KST.Fibration
