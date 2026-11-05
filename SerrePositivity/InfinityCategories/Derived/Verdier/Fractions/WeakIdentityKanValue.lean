module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakIdentitySpanPoint
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanFiberComparison
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
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の恒等 span を、零単体の初頂点に終点表示を揃えただけの同じ点として保持する。 -/
def weakIdentityFixedSpanAtZeroIndex :
    (fixedMarkedSpans B.obj (weakEquivalences i) x
      ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
        (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x)))) _⦋0⦌ :=
  (eqToHom (congrArg (fun y => fixedMarkedSpans B.obj (weakEquivalences i) x y)
    (transportSimplexFirstVertexMap_zeroIndex x).symm)).app (Opposite.op ⦋0⦌)
      (weakIdentityFixedSpan h x)

/-- 元の恒等点を strict Kan 値から戻すと、同じ元の固定分数点の置換単位像を厳密に回収する。 -/
theorem weakIdentityKanPoint_valueComparison :
    (weakSpanKanValueComparison i x (transportSimplexIndex (n := ⦋0⦌) x)).app
      (Opposite.op ⦋0⦌) (weakIdentityKanPoint h x) =
      (F2.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
        (weakIdentityFixedSpanAtZeroIndex h x) := by
  let c := transportSimplexIndex (n := ⦋0⦌) x
  let s := weakSpanSimplexFiberIso i x c
  have hn := congrArg (fun m => m.app (Opposite.op ⦋0⦌)
    (weakIdentitySimplexFiberPoint h x))
    (F2.continuousKanReplacementUnit.naturality s.inv)
  have hi : s.inv.app (Opposite.op ⦋0⦌) (weakIdentitySimplexFiberPoint h x) =
      weakIdentityFixedSpanAtZeroIndex h x :=
    congrArg (fun m => m.app (Opposite.op ⦋0⦌) (weakIdentityFixedSpanAtZeroIndex h x))
      s.hom_inv_id
  change (strictKanCompletion.map s.inv).app (Opposite.op ⦋0⦌)
    ((cocartesianKanDiagramFiberComparison (weakSpanSimplexProjection i x) c).app
      (Opposite.op ⦋0⦌) (weakIdentityKanPoint h x)) = _
  rw [weakIdentityKanPoint_evaluate]
  exact hn.symm.trans (congrArg
    ((F2.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)) hi)

/-- 同じ全自然変換の恒等点での像は、元の固定分数 coslice 評価の単位像そのもの。 -/
theorem weakIdentityKanMappingComparison_evaluate :
    (fractionSimplexKanValueComparison (q := q) x
      (transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
      (((weakSpanKanMappingComparison h x).app
        (transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
          (weakIdentityKanPoint h x)) =
      (F2.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
        ((fixedFractionCosliceEvaluation q.hom (weakEquivalences i) h.inverts x
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
            (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x)))).app (Opposite.op ⦋0⦌)
              (weakIdentityFixedSpanAtZeroIndex h x)) := by
  let hq : InvertsEdges q.hom (weakEquivalences i) := h.inverts
  let c := transportSimplexIndex (n := ⦋0⦌) x
  let f := fixedFractionCosliceEvaluation q.hom (weakEquivalences i) hq x
    ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))
  have he := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (weakIdentityKanPoint h x))
    (weakSpanKanMappingComparison_value h x c)
  have hn := congrArg (fun m => m.app (Opposite.op ⦋0⦌)
    (weakIdentityFixedSpanAtZeroIndex h x)) (F2.continuousKanReplacementUnit.naturality f)
  exact he.trans ((congrArg ((strictKanCompletion.map f).app (Opposite.op ⦋0⦌))
    (weakIdentityKanPoint_valueComparison h x)).trans hn.symm)

/-- 同じ coslice 側の Kan 値を評価し、初頂点の表示を元の x の商像へ厳密に揃える。 -/
def weakIdentityKanTargetEvaluation :
    ((fractionSimplexKanMappingDiagram q.hom x).obj
      (transportSimplexIndex (n := ⦋0⦌) x)).obj ⟶
      F2.continuousKanReplacement.obj (vertexFiber
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
        (q.hom.app (Opposite.op ⦋0⦌) x)) :=
  fractionSimplexKanValueComparison (q := q) x (transportSimplexIndex (n := ⦋0⦌) x) ≫
    F2.continuousKanReplacement.map (eqToHom (congrArg (vertexFiber
      (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
      (congrArg (q.hom.app (Opposite.op ⦋0⦌)) (transportSimplexFirstVertexMap_zeroIndex x))))

/-- 同じ自然変換の恒等点の像を元の fiber へ戻すと、元の固定分数評価点を厳密に回収する。 -/
theorem weakIdentityKanTargetEvaluation_recover :
    (weakIdentityKanTargetEvaluation (q := q) x).app (Opposite.op ⦋0⦌)
      (((weakSpanKanMappingComparison h x).app
        (transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
          (weakIdentityKanPoint h x)) =
      (F2.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
        ((fixedFractionCosliceEvaluation q.hom (weakEquivalences i) h.inverts x x).app
          (Opposite.op ⦋0⦌) (weakIdentityFixedSpan h x)) := by
  let hq : InvertsEdges q.hom (weakEquivalences i) := h.inverts
  let t := eqToHom (congrArg (vertexFiber
    (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x))))
    (congrArg (q.hom.app (Opposite.op ⦋0⦌)) (transportSimplexFirstVertexMap_zeroIndex x)))
  let v := (fixedFractionCosliceEvaluation q.hom (weakEquivalences i) hq x
    ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
      (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x)))).app (Opposite.op ⦋0⦌)
        (weakIdentityFixedSpanAtZeroIndex h x)
  have he := congrArg ((F2.continuousKanReplacement.map t).app (Opposite.op ⦋0⦌))
    (weakIdentityKanMappingComparison_evaluate h x)
  have hn := congrArg (fun m => m.app (Opposite.op ⦋0⦌) v)
    (F2.continuousKanReplacementUnit.naturality t)
  have hv := fixedFractionCosliceEvaluation_transport_vertex q.hom (weakEquivalences i)
    hq x (transportSimplexFirstVertexMap_zeroIndex x) (weakIdentityFixedSpan h x)
  exact he.trans (hn.symm.trans (congrArg
    ((F2.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)) hv))

/-- 同じ全比較の元の恒等点の像は、実 coslice fiber の Kan 模型内で恒等点と同値。 -/
def weakIdentityKanMappingComparisonUnitIso : VertexIso
    ((weakIdentityKanTargetEvaluation (q := q) x).app (Opposite.op ⦋0⦌)
      (((weakSpanKanMappingComparison h x).app
        (transportSimplexIndex (n := ⦋0⦌) x)).app (Opposite.op ⦋0⦌)
          (weakIdentityKanPoint h x)))
    ((F2.continuousKanReplacementUnit.app _).app (Opposite.op ⦋0⦌)
      (edgeToCosliceFiberVertex (SSet.Edge.id (q.hom.app (Opposite.op ⦋0⦌) x)))) := by
  have e := VertexIso.map (identityFixedFractionCosliceEvaluationIso q.hom
    (weakEquivalences i) h.inverts x (weakIdentitySpan_mem h x))
      (F2.continuousKanReplacementUnit.app _)
  exact eqToIso (congrArg HomotopyCategory.mk (weakIdentityKanTargetEvaluation_recover h x)) ≪≫ e

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityFixedSpanAtZeroIndex := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparison_evaluate := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanMappingComparison_evaluate

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanPoint_valueComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanPoint_valueComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanTargetEvaluation (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanTargetEvaluation := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanTargetEvaluation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanTargetEvaluation_recover := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanTargetEvaluation_recover

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityFixedSpanAtZeroIndex._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityFixedSpanAtZeroIndex._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanMappingComparisonUnitIso._proof_7 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanMappingComparisonUnitIso._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakIdentityKanTargetEvaluation._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakIdentityKanTargetEvaluation._proof_1
