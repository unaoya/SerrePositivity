module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：元の任意の冪等完備化と充満忠実性は、inner 仮定なしで反転できる。
方針：元の頂点像への同値と全部分圏の包含へ因子化し、保存済みの反転を合成する。
規約：元の全射そのものの反転を結論する。
使われ方：零対象の保存の始対象側への双対化。

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

/-- 元の充満忠実な射は、inner 仮定なしで反転しても充満忠実。 -/
lemma isFullyFaithful_op_of_fullyFaithful {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (SSet.opFunctor.map f) := by
  let P := fun y ↦ ∃ x, f.app (Opposite.op ⦋0⦌) x = y
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P f (fun x ↦ ⟨x, rfl⟩)
  let i := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P).ι
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.fullSubcomplexVertexImageLift_isQCatEquivalence f hf
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι Y P
  have : InnerFibration i := inferInstanceAs (InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P).ι)
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_op he).isFullyFaithful.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isFullyFaithful_op i hi)
  have hfac : e ≫ i = f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have ho : SSet.opFunctor.map e ≫ SSet.opFunctor.map i = SSet.opFunctor.map f :=
    (SSet.opFunctor.map_comp e i).symm.trans (congrArg SSet.opFunctor.map hfac)
  exact ho ▸ h

/-- 元の任意の冪等完備化は、単射性・inner 仮定なしで同じ元の反転射へ移る。 -/
lemma IsIdempotentCompletion.op_general {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (SSet.opFunctor.map f) := by
  refine ⟨hf.1.op, isFullyFaithful_op_of_fullyFaithful f hf.2.1, ?_⟩
  intro d
  obtain ⟨c, hc⟩ := hf.2.2 (SSet.opObjEquiv d)
  refine ⟨SSet.opObjEquiv.symm c, ?_⟩
  rw [SSet.opFunctor_map, Equiv.apply_symm_apply]
  simpa only [Equiv.symm_apply_apply] using hc.op

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
