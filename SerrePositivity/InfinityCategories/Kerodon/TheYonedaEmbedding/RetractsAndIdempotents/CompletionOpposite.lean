module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OppositeLifting

/-!
概要：元の充満忠実な inner fibration の冪等完備化を反転する。
方針：coherent 完備性・写像空間の充満忠実性・指定頂点の retract 条件を反転する。
規約：同じ元の射を反転し、元の全条件を実際に証明して移す。
使われ方：HTT 5.1.4.6 の左右の cofinal 性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の充満忠実な inner fibration の冪等完備化は、同じ元の反転射でも冪等完備化。 -/
lemma IsIdempotentCompletion.op {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (f : C ⟶ D) [InnerFibration f] (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (SSet.opFunctor.map f) := by
  refine ⟨hf.1.op, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isFullyFaithful_op f hf.2.1, ?_⟩
  intro d
  obtain ⟨c, hc⟩ := hf.2.2 (SSet.opObjEquiv d)
  refine ⟨SSet.opObjEquiv.symm c, ?_⟩
  have h := hc.op
  rw [SSet.opFunctor_map, Equiv.apply_symm_apply]
  simpa only [Equiv.symm_apply_apply] using h

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
