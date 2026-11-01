module

public import SerrePositivity.InfinityCategories.ModelBridge.PaddedBackwardEmbeddingComparison
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
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory HomotopicalAlgebra SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include cof in
lemma paddedForwardDiagramMap_isWeakHomotopyEquivalence (w : Word) :
    IsWeakHomotopyEquivalence
      ((paddedForwardDiagramMap (graphDiagram (weakEquivalences C) X Y)).app w) := by
  apply paddedBackwardEmbedding_isWeakHomotopyEquivalence X Y cof
    (Word.forwardInclusion w) (Word.forwardInclusion_injective w)
  intro j hj
  cases hd : w.direction j with
  | forward => exact False.elim (hj ((Word.forwardInclusion_range w j).2 hd))
  | backward => rfl

end SerrePositivity.EInfinity.Hammock
