module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SliceComplete

/-!
概要：元の全部分圏による冪等完備化は、任意の図式の slice 上でも冪等完備化。
方針：元の slice 射影の右 fibration 性と、元の pullback の底変換定理を適用する。
規約：充満忠実な inner fibration の仮定を明示し、特に全部分複体の包含を扱う。
使われ方：HTT 5.1.4.4、Quillen A による cofinal 性の準備。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の冪等完備化の包含を、任意の元の slice へ引き戻しても冪等完備化。 -/
lemma IsIdempotentCompletion.sliceOver {C D K : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) [InnerFibration f]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) (p : K ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (pullback.snd f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pullback_rightFibration f hf (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.1.4.4" (partial := stronger-hyp) "仮定：冪等完備化を与える関手 f と標的の図式（Lean が強い：f に内ファイブレーション性を要求）。結論：同じスライス射影に沿って引き戻した関手も冪等完備化を与える（一致する場合）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.sliceOver
