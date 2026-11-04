module
public import SerrePositivity.KST.Fibration.WeakSpanKanMappingComparison
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionCosliceFiberComparison
public import SerrePositivity.KST.Fibration.StrictKanPostEvaluation

/-! # 元の coherent な分数比較は、全ての値で同じ固定分数評価を回収する -/

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
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌) (c : TransportSimplexCategory B.obj)

/-- coslice 側の同じ strict Kan 値を、元の coslice fiber の Kan 模型へ評価する。 -/
def fractionSimplexKanValueComparison :
    ((fractionSimplexKanMappingDiagram q.hom x).obj c).obj ⟶
      (strictKanCompletion.obj (vertexFiber
        (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
        (q.hom.app (Opposite.op ⦋0⦌)
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))))).obj :=
  cocartesianKanDiagramFiberComparison (fractionSimplexCosliceProjection q.hom x) c ≫
    strictKanCompletion.map (vertexFiberPullbackIso _
      (transportSimplexFirstVertexMap B.obj ≫ q.hom) (nerveVertex c)).hom

/-- 同じ値の比較は実際の Kan 同値。 -/
theorem fractionSimplexKanValueComparison_isQCatEquivalence :
    IsQCatEquivalence (fractionSimplexKanValueComparison (q := q) x c) :=
  (cocartesianKanDiagramFiberComparison_isQCatEquivalence
    (fractionSimplexCosliceProjection q.hom x) c).comp
      (strictKanCompletion_map_isQCatEquivalence _ (by infer_instance))

/-- 同じ strict Kan 比較を評価すると、元の固定分数 coslice 評価の Kan 置換と厳密に可換。 -/
theorem weakSpanKanMappingComparison_value :
    (weakSpanKanMappingComparison h x).app c ≫
      fractionSimplexKanValueComparison (q := q) x c =
      weakSpanKanValueComparison i x c ≫ strictKanCompletion.map
        (fixedFractionCosliceEvaluation q.hom (weakEquivalences i) h.inverts x
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))) := by
  let hq : InvertsEdges q.hom (weakEquivalences i) := h.inverts
  let p := weakSpanSimplexProjection i x
  let t := fractionSimplexCosliceProjection q.hom x
  let f := fractionCosliceBaseChange q.hom (weakEquivalences i) hq x
    (transportSimplexFirstVertexMap B.obj)
  have hft : f ≫ t = p := fractionCosliceBaseChange_snd q.hom (weakEquivalences i) hq x _
  let v := (vertexFiberPullbackIso
    (sliceUnderProjection (yonedaEquiv.symm (q.hom.app (Opposite.op ⦋0⦌) x)))
    (transportSimplexFirstVertexMap B.obj ≫ q.hom) (nerveVertex c)).hom
  let R : SSet.{u} ⥤ SSet.{u} := strictKanCompletion ⋙ kanObjectForget
  have he := congrArg R.map (strictTransportPostToLeftFibration_evaluate p t f hft c)
  have hf : vertexFiberMap p t f hft (nerveVertex c) ≫ v =
      (weakSpanSimplexFiberIso i x c).inv ≫
        fixedFractionCosliceEvaluation q.hom (weakEquivalences i) hq x
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)) :=
    fractionCosliceFiberMap_unfixed q.hom (weakEquivalences i) hq x _ _
  change R.map ((strictTransportPostToLeftFibration p t f hft).app c) ≫
      (R.map (SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate t c) ≫ R.map v) =
    (R.map (SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate p c) ≫
      R.map (weakSpanSimplexFiberIso i x c).inv) ≫
        R.map (fixedFractionCosliceEvaluation q.hom (weakEquivalences i) hq x
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c)))
  rw [R.map_comp, R.map_comp] at he
  rw [← Category.assoc, he, Category.assoc, ← R.map_comp, hf, R.map_comp, Category.assoc]

end SerrePositivity.KST.Fibration
