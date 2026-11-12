module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RightFibrationRetracts
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.FibrationComplete
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBaseChange

/-!
概要：充満忠実な inner fibration による冪等完備化は、右 fibration に沿う底変換で保たれる。
方針：全体の冪等完備性と充満忠実性を反映し、指定した元の retract を持ち上げる。
規約：元の pullback と射影を保持する。全部分複体の包含に適用できる。
使われ方：HTT 5.1.4.4 の元の slice 上の冪等完備化。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の充満忠実な inner fibration の冪等完備化を右 fibration へ底変換する。 -/
lemma IsIdempotentCompletion.pullback_rightFibration {C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (f : C ⟶ D) [InnerFibration f] (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
    (q : E ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (pullback.snd f q) := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_of_rightFibration q hf.1, hf.2.1.pullback_snd q, ?_⟩
  intro e
  obtain ⟨c, ⟨r⟩⟩ := hf.2.2 (q.app (Opposite.op ⦋0⦌) e)
  obtain ⟨z, hz, hez⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.rightFibration_retract_lift q e
    (f.app (Opposite.op ⦋0⦌) c) r
  have h : SSet.yonedaEquiv.symm c ≫ f = SSet.yonedaEquiv.symm z ≫ q := by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hz.symm
  let v := pullback.lift (SSet.yonedaEquiv.symm c) (SSet.yonedaEquiv.symm z) h
  have hv : (pullback.snd f q).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv v) = z := by
    have hh := congrArg SSet.yonedaEquiv
      (pullback.lift_snd (SSet.yonedaEquiv.symm c) (SSet.yonedaEquiv.symm z) h)
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hh
  exact ⟨SSet.yonedaEquiv v, hv.symm ▸ hez⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
