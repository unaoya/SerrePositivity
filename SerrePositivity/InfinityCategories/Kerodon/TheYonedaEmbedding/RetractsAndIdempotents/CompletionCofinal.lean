module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionLeftCofinal
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionOpposite

/-!
概要：元の全部分圏による冪等完備化の包含は、余極限を計算する向きにも cofinal。
方針：同じ反転射の極限側の Quillen A を、元の射の right cofinal 性へ戻す。
規約：元の包含そのものを判定し、普遍性の仮定を追加しない。
使われ方：HTT 5.1.4.6、元の全標準左 Kan 余錐の普遍性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の全部分圏の冪等完備化の包含は right cofinal。 -/
lemma IsIdempotentCompletion.isRightCofinal {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) [InnerFibration f]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.isLeftCofinal (SSet.opFunctor.map f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.op f hf)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_iff_isLeftCofinal_op f).mpr h

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
