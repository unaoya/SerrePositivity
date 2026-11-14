module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.PaddedBackwardEmbeddingComparison
public import SerrePositivity.EInfinity.Hammock.ProperFractionDiagrams

/-!
# 元の paddedForwardDiagramMap の全成分の弱同値性

概要：元の任意の語で padded な forward 部分語の包含の graph 写像は弱同値となる。
方針：元の forwardInclusion は backward 列だけを欠く単射なので、有限挿入を適用する。
規約：元の自然変換の成分自身を結論にし、forward 部分語が空の場合も含む。
使われ方：proper な元の全語の余極限への比較。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra _root_.SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include cof in
lemma paddedForwardDiagramMap_isWeakHomotopyEquivalence (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.EInfinity.Hammock.paddedForwardDiagramMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y)).app w) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.paddedBackwardEmbedding_isWeakHomotopyEquivalence X Y cof
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion_injective w)
  intro j hj
  cases hd : w.direction j with
  | forward => exact False.elim (hj ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion_range w j).2 hd))
  | backward => rfl

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
