module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionSlice
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionTerminalContraction
public import SerrePositivity.InfinityCategories.F1B.QuillenALeft
public import SerrePositivity.InfinityCategories.F1B.KanSliceIdentityTerminal

/-!
概要：元の全部分圏の冪等完備化の包含は、極限を計算する向きに cofinal。
方針：元の各 slice の冪等完備化と恒等錐の終対象性から、元の引き戻しを弱可縮にする。
規約：元の包含と元の slice 射影の pullback を使用し、実際の Quillen A を適用する。
使われ方：HTT 5.1.4.6 の双対、全関手の Kan 性の準備。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の冪等完備化の包含で引き戻した各点上の元の slice は弱可縮。 -/
lemma IsIdempotentCompletion.slice_isWeaklyContractible {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) [InnerFibration f]
    (hf : IsIdempotentCompletion f) (d : D _⦋0⦌) :
    IsWeaklyContractible (pullback f (sliceOverProjection (SSet.yonedaEquiv.symm d))) := by
  let q := sliceOverProjection (SSet.yonedaEquiv.symm d)
  have : InnerFibration (pullback.snd f q) :=
    ⟨innerFibrations.pullback_snd f q (InnerFibration.mem (q := f))⟩
  have : Quasicategory (pullback f q) := quasicategory_of_innerFibration (pullback.snd f q)
  exact IsIdempotentCompletion.isWeaklyContractible_of_terminal (pullback.snd f q)
    (IsIdempotentCompletion.sliceOver f hf (SSet.yonedaEquiv.symm d)) (sliceIdentityCone d)
    (F1B.kanSliceIdentityCone_isTerminalVertex d)

/-- 元の全部分圏の冪等完備化の包含は left cofinal。 -/
lemma IsIdempotentCompletion.isLeftCofinal {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) [InnerFibration f]
    (hf : IsIdempotentCompletion f) : IsLeftCofinal f :=
  isLeftCofinal_of_weaklyContractible_slices f
    (IsIdempotentCompletion.slice_isWeaklyContractible f hf)

end SerrePositivity.InfinityCategories.F2.Idempotent
