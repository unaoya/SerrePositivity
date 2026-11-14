module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSemifreeEvaluationComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal

/-!
概要：元のstrict半自由図式の直和全複体を、元の自然変換を含む全族で評価する。
方針：通常複体へ忘れる関手と既存の直和全複体関手を合成してnerveを取る。
規約：頂点ごとに選ぶ実現とはせず、射と高次単体の全てを同じ関手で写す。
使われ方：3b-3 R6、指定実現とnative余錐の全族比較の実現側。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A]

/-- 元の半自由strict図式と自然変換の、非正規化直和全複体の同じ通常関手。 -/
def strictSemifreeRealizationComplex :
    StrictSemifreeDiagram A SimplexCategoryᵒᵖ ⥤ Complex A :=
  strictSemifreeUnderlyingComplex A .simplicial ⋙ directSumTotalFunctor A

/-- 同じ実現関手の全nerveを、指定されたD(A)へ評価した全族。 -/
def strictSemifreeRealizationFamily :
    nerve (StrictSemifreeDiagram A SimplexCategoryᵒᵖ) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  nerveMap (strictSemifreeRealizationComplex A) ≫ complexDerivedEvaluation A

/-- 全族の頂点は元の同じ直和全複体の評価である。 -/
lemma strictSemifreeRealizationFamily_vertex (F : StrictSemifreeDiagram A SimplexCategoryᵒᵖ) :
    (strictSemifreeRealizationFamily A).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ F) =
      (complexDerivedEvaluation A).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ ((strictSemifreeRealizationComplex A).obj F)) := by
  change (complexDerivedEvaluation A).app (Opposite.op ⦋0⦌)
    ((nerveMap (strictSemifreeRealizationComplex A)).app _ (ComposableArrows.mk₀ F)) = _
  rw [nerveMap_app_mk₀]

/-- 全族の辺は、元の自然変換の全複体への像を評価した同じ辺である。 -/
lemma strictSemifreeRealizationFamily_edge {F G : StrictSemifreeDiagram A SimplexCategoryᵒᵖ}
    (f : F ⟶ G) :
    (strictSemifreeRealizationFamily A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) =
      (complexDerivedEvaluation A).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ ((strictSemifreeRealizationComplex A).map f)) := by
  change (complexDerivedEvaluation A).app (Opposite.op ⦋1⦌)
    ((nerveMap (strictSemifreeRealizationComplex A)).app _ (ComposableArrows.mk₁ f)) = _
  rw [nerveMap_app_mk₁]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
