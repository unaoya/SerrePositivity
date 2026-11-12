module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakIdentitySpanPoint
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakSpanKanFiberComparison
public import SerrePositivity.KST.Fibration.FixedFractionCosliceTransport
public import SerrePositivity.KST.Fibration.IdentityCosliceEvaluation

/-! # 同じ strict Kan 比較の恒等点における評価を、元の固定分数点で計算する -/

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

/-- 元の恒等 span を、零単体の初頂点に終点表示を揃えただけの同じ点として保持する。 -/
def weakIdentityFixedSpanAtZeroIndex :
    (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)))) _⦋0⦌ :=
  (eqToHom (congrArg (fun y => fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x).symm)).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan h x)

/-- 元の恒等点を strict Kan 値から戻すと、同じ元の固定分数点の置換単位像を厳密に回収する。 -/
theorem weakIdentityKanPoint_valueComparison :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanValueComparison i x (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex h x) := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexFiberIso i x c
  have hn := congrArg (fun m => m.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentitySimplexFiberPoint h x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality s.inv)
  have hi : s.inv.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentitySimplexFiberPoint h x) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex h x :=
    congrArg (fun m => m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex h x))
      s.hom_inv_id
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion.map s.inv).app (Opposite.op ⦋0⦌)
    ((cocartesianKanDiagramFiberComparison (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexProjection i x) c).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint_evaluate]
  exact hn.symm.trans (congrArg
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)) hi)

/-- 同じ全自然変換の恒等点での像は、元の固定分数 coslice 評価の単位像そのもの。 -/
theorem weakIdentityKanMappingComparison_evaluate :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanValueComparison (q := q) x
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
      (((weakSpanKanMappingComparison h x).app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionCosliceEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)))).app (Opposite.op ⦋0⦌)
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex h x)) := by
  let hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) := h.inverts
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x
  let f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionCosliceEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) hq x
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))
  have he := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanMappingComparison_value h x c)
  have hn := congrArg (fun m => m.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex h x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality f)
  exact he.trans ((congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion.map f).app (Opposite.op ⦋0⦌))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint_valueComparison h x)).trans hn.symm)

/-- 同じ coslice 側の Kan 値を評価し、初頂点の表示を元の x の商像へ厳密に揃える。 -/
def weakIdentityKanTargetEvaluation :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)).obj ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
        (q.hom.app (Opposite.op ⦋0⦌) x)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanValueComparison (q := q) x (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
      (congrArg (q.hom.app (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x))))

/-- 同じ自然変換の恒等点の像を元の fiber へ戻すと、元の固定分数評価点を厳密に回収する。 -/
theorem weakIdentityKanTargetEvaluation_recover :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanTargetEvaluation (q := q) x).app (Opposite.op ⦋0⦌)
      (((weakSpanKanMappingComparison h x).app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionCosliceEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x x).app
          (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan h x)) := by
  let hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) := h.inverts
  let t := eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
    (congrArg (q.hom.app (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x)))
  let v := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionCosliceEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) hq x
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)))).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex h x)
  have he := congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map t).app (Opposite.op ⦋0⦌))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanMappingComparison_evaluate h x)
  have hn := congrArg (fun m => m.app (Opposite.op ⦋0⦌) v)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality t)
  have hv := fixedFractionCosliceEvaluation_transport_vertex q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
    hq x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpan h x)
  exact he.trans (hn.symm.trans (congrArg
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)) hv))

/-- 同じ全比較の元の恒等点の像は、実 coslice fiber の Kan 模型内で恒等点と同値。 -/
def weakIdentityKanMappingComparisonUnitIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanTargetEvaluation (q := q) x).app (Opposite.op ⦋0⦌)
      (((weakSpanKanMappingComparison h x).app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint h x)))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeToCosliceFiberVertex (SSet.Edge.id (q.hom.app (Opposite.op ⦋0⦌) x)))) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (identityFixedFractionCosliceEvaluationIso q.hom
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentitySpan_mem h x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app _)
  exact eqToIso (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanTargetEvaluation_recover h x)) ≪≫ e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityFixedSpanAtZeroIndex := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparison_evaluate := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanMappingComparison_evaluate

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanPoint_valueComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanPoint_valueComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanTargetEvaluation (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanTargetEvaluation := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanTargetEvaluation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanTargetEvaluation_recover := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanTargetEvaluation_recover

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityFixedSpanAtZeroIndex._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanTargetEvaluation._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakIdentityKanTargetEvaluation._proof_1
