module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.KST.Fibration.WeakSpanKanMappingComparison
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionCosliceFiberComparison
public import SerrePositivity.KST.Fibration.StrictKanPostEvaluation

/-! # 元の coherent な分数比較は、全ての値で同じ固定分数評価を回収する -/

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
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌) (c : TransportSimplexCategory B.obj)

/-- coslice 側の同じ strict Kan 値を、元の coslice fiber の Kan 模型へ評価する。 -/
def fractionSimplexKanValueComparison :
    ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x).obj c).obj ⟶
      (_root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion.obj (vertexFiber
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
        (q.hom.app (Opposite.op ⦋0⦌)
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))))).obj :=
  cocartesianKanDiagramFiberComparison (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexCosliceProjection q.hom x) c ≫
    _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion.map (vertexFiberPullbackIso _
      (transportSimplexFirstVertexMap B.obj ≫ q.hom) (nerveVertex c)).hom

/-- 同じ値の比較は実際の Kan 同値。 -/
theorem fractionSimplexKanValueComparison_isQCatEquivalence :
    IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanValueComparison (q := q) x c) :=
  (cocartesianKanDiagramFiberComparison_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexCosliceProjection q.hom x) c).comp
      (_root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion_map_isQCatEquivalence _ (by infer_instance))

/-- 同じ strict Kan 比較を評価すると、元の固定分数 coslice 評価の Kan 置換と厳密に可換。 -/
theorem weakSpanKanMappingComparison_value :
    (weakSpanKanMappingComparison h x).app c ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanValueComparison (q := q) x c =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanValueComparison i x c ≫ _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion.map
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))) := by
  let hq : InvertsEdges q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) := h.inverts
  let p := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexProjection i x
  let t := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexCosliceProjection q.hom x
  let f := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionCosliceBaseChange q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) hq x
    (transportSimplexFirstVertexMap B.obj)
  have hft : f ≫ t = p := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionCosliceBaseChange_snd q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) hq x _
  let v := (vertexFiberPullbackIso
    (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
    (transportSimplexFirstVertexMap B.obj ≫ q.hom) (nerveVertex c)).hom
  let R : SSet.{u} ⥤ SSet.{u} := _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion ⋙ kanObjectForget
  have he := congrArg R.map (strictTransportPostToLeftFibration_evaluate p t f hft c)
  have hf : vertexFiberMap p t f hft (nerveVertex c) ≫ v =
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexFiberIso i x c).inv ≫
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) hq x
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)) :=
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionCosliceFiberMap_unfixed q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) hq x _ _
  change R.map ((strictTransportPostToLeftFibration p t f hft).app c) ≫
      (R.map (SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate t c) ≫ R.map v) =
    (R.map (SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate p c) ≫
      R.map (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSimplexFiberIso i x c).inv) ≫
        R.map (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) hq x
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)))
  rw [R.map_comp, R.map_comp] at he
  rw [← Category.assoc, he, Category.assoc, ← R.map_comp, hf, R.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanValueComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionSimplexKanValueComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanValueComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionSimplexKanValueComparison_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanValueComparison_isQCatEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanMappingComparison_value := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanMappingComparison_value

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionSimplexKanValueComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanValueComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionSimplexKanValueComparison._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanValueComparison._proof_2
