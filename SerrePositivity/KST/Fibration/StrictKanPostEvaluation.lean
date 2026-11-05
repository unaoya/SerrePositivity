module
public import SerrePositivity.KST.Fibration.StrictTransportPostEvaluation

/-! # 同じ strict Kan 自然変換は、元の fiber 評価と厳密に可換 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 元の fiber 評価の可換四角形を、同じ関手的 Kan 置換が厳密に保つ。 -/
theorem strictKanTransportPostToLeftFibration_evaluate
    {I : Type u} [Category.{u} I] {E T : SSet.{u}}
    (p : E ⟶ nerve I) (q : T ⟶ nerve I) [LeftFibration q]
    (f : E ⟶ T) (hf : f ≫ q = p) (c : I) :
    (strictKanTransportPostToLeftFibration p q f hf).app c ≫
      cocartesianKanDiagramFiberComparison q c =
      cocartesianKanDiagramFiberComparison p c ≫
        _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion.map (vertexFiberMap p q f hf (nerveVertex c)) := by
  change _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion.map ((strictTransportPostToLeftFibration p q f hf).app c) ≫
      _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion.map (SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate q c) =
    _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion.map (SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate p c) ≫
      _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion.map (vertexFiberMap p q f hf (nerveVertex c))
  rw [← Functor.map_comp, ← Functor.map_comp,
    strictTransportPostToLeftFibration_evaluate]

end SerrePositivity.KST.Fibration
