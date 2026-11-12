module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.TwistedSourceElementsEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.TwistedIdentityFiberEquivalence

/-!
概要：同じ始点を持つ全 twisted arrow 族の大域評価そのものは弱同値。
方針：始対象上の fiber 包含の弱同値と、同じ恒等点評価の同値を二対三則で消去する。
規約：元の大域切断と同じ射を検査する。密度余錐との比較は別工程。
使われ方：元の小さい密度余錐の評価写像の弱同値性の全空間側。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 構成済みの同じ全族の評価は、元の反転した fiber への弱ホモトピー同値。 -/
lemma twistedSourceElementsEvaluation_isWeakHomotopyEquivalence
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsEvaluation p b) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsIdentityInclusion_isWeakHomotopyEquivalence p b).cancel_left
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedSourceElementsEvaluation_identity]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedIdentityFiberEvaluation_isWeakHomotopyEquivalence p b

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
