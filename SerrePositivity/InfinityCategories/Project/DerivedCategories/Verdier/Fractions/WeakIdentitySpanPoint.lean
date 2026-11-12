module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.IdentityMarkedSpan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakSpanKanDiagram
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakDenominatorSpanTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertexNaturality

/-! # 元の恒等 span を、同じ strict section と Kan 分数図式の実際の点へ移す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

include h in
/-- 元の恒等辺は、同じ商関手が反転する W 分母。 -/
theorem weakIdentitySpan_mem : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1 ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakEquivalences_eq_invertedEdges h]
  exact invertedEdges_constant q.hom x

/-- 元の両端固定分数空間の恒等点。 -/
def weakIdentityFixedSpan : (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x x) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityFixedMarkedSpan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentitySpan_mem h x)

/-- 零単体を添字とする初頂点は、元の同じ頂点そのもの。 -/
theorem transportSimplexFirstVertexMap_zeroIndex {X : SSet.{u}} (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap X).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)) = x := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_vertex]
  have he : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply SSet.stdSimplex.ext
    intro k
    apply Fin.ext
    omega
  rw [he, yonedaEquiv_symm_app_id]

/-- 恒等 span を、全単体圏上の同じ厳密 fiber 同型で運んだ点。 -/
def weakIdentitySimplexFiberPoint :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexProjection i x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x))) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexFiberIso i x (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)).hom.app
    (Opposite.op ⦋0⦌)
      ((eqToHom (congrArg (fun y => fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x).symm)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan h x))

/-- 同じ恒等射評価の自明 Kan fibration の切断を選ぶ。 -/
def weakIdentityStrictEvaluationSection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexProjection i x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexProjection i x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexProjection i x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)))

/-- 元の恒等 span を厳密に評価値とする、全 cocartesian section の実際の点。 -/
def weakIdentityStrictSectionPoint :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexProjection i x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityStrictEvaluationSection (i := i) x).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentitySimplexFiberPoint h x)

/-- 評価は、構成に用いた同じ恒等 span の fiber 点を厳密に回収する。 -/
theorem weakIdentityStrictSectionPoint_evaluate :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexProjection i x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityStrictSectionPoint h x) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentitySimplexFiberPoint h x :=
  congrArg (fun m => m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentitySimplexFiberPoint h x))
    (Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexProjection i x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x))))

/-- 同じ strict Kan 分数図式の値における、元の恒等 span からの指定点。 -/
def weakIdentityKanPoint :
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)).obj) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityStrictSectionPoint h x)

/-- Kan 置換後の同じ評価も、元の恒等 span の fiber 点の単位像を厳密に回収する。 -/
theorem weakIdentityKanPoint_evaluate :
    (cocartesianKanDiagramFiberComparison (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexProjection i x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentitySimplexFiberPoint h x) := by
  have hn := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityStrictSectionPoint h x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportEvaluate (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexProjection i x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)))
  exact hn.symm.trans (congrArg
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityStrictSectionPoint_evaluate h x))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportSimplexFirstVertexMap_zeroIndex := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityFixedSpan := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanPoint := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanPoint_evaluate := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint_evaluate

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentitySimplexFiberPoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentitySimplexFiberPoint := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentitySimplexFiberPoint

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentitySpan_mem := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentitySpan_mem

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityStrictEvaluationSection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityStrictEvaluationSection := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityStrictEvaluationSection

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityStrictSectionPoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityStrictSectionPoint := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityStrictSectionPoint

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityStrictSectionPoint_evaluate := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityStrictSectionPoint_evaluate

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentitySimplexFiberPoint._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentitySimplexFiberPoint._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentitySimplexFiberPoint._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentitySimplexFiberPoint._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityStrictEvaluationSection._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityStrictEvaluationSection._proof_1
