module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionSlice
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionTerminalContraction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenALeft
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceIdentityTerminal

/-!
概要：元の全部分圏の冪等完備化の包含は、極限を計算する向きに cofinal。
方針：元の各 slice の冪等完備化と恒等錐の終対象性から、元の引き戻しを弱可縮にする。
規約：元の包含と元の slice 射影の pullback を使用し、実際の Quillen A を適用する。
使われ方：HTT 5.1.4.6 の双対、全関手の Kan 性の準備。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の冪等完備化の包含で引き戻した各点上の元の slice は弱可縮。 -/
lemma IsIdempotentCompletion.slice_isWeaklyContractible {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) [InnerFibration f]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) (d : D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (pullback f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm d))) := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm d)
  have : InnerFibration (pullback.snd f q) :=
    ⟨innerFibrations.pullback_snd f q (InnerFibration.mem (q := f))⟩
  have : Quasicategory (pullback f q) := quasicategory_of_innerFibration (pullback.snd f q)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.isWeaklyContractible_of_terminal (pullback.snd f q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.sliceOver f hf (SSet.yonedaEquiv.symm d)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceIdentityCone_isTerminalVertex d)

/-- 元の全部分圏の冪等完備化の包含は left cofinal。 -/
lemma IsIdempotentCompletion.isLeftCofinal {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) [InnerFibration f]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_weaklyContractible_slices f
    (IsIdempotentCompletion.slice_isWeaklyContractible f hf)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
