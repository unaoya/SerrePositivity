module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：元の任意の冪等完備化への制限は、全関手空間で充満忠実。
方針：元の頂点像の全部分圏へ因子化し、元の同値と全部分圏の包含への制限を合成する。
規約：元の射の単射性や inner fibration 性は仮定しない。
使われ方：元の idemYoneda に沿う HTT 5.1.4.9 の充満忠実性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の冪等完備化の頂点像の全部分圏の包含も、同じ標的の冪等完備化。 -/
lemma IsIdempotentCompletion.vertexImage {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices D
      (fun y ↦ ∃ x, f.app (Opposite.op ⦋0⦌) x = y)).ι := by
  refine ⟨hf.1, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _, ?_⟩
  intro d
  obtain ⟨c, hc⟩ := hf.2.2 d
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (fun y ↦ ∃ x, f.app (Opposite.op ⦋0⦌) x = y) f
    (fun x ↦ ⟨x, rfl⟩)
  exact ⟨e.app (Opposite.op ⦋0⦌) c, hc⟩

/-- 元の任意の冪等完備化に沿う同じ制限は、全関手の全写像空間で充満忠実。 -/
lemma IsIdempotentCompletion.pre_isFullyFaithful_general {C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (f : C ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre f).app E) := by
  let P := fun y ↦ ∃ x, f.app (Opposite.op ⦋0⦌) x = y
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P f (fun x ↦ ⟨x, rfl⟩)
  let i := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices D P).ι
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion i := IsIdempotentCompletion.vertexImage f hf
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isFullyFaithful (D := E) i hi
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.fullSubcomplexVertexImageLift_isQCatEquivalence f hf.2.1
  have hfac : e ≫ i = f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  rw [← hfac, pre_map, NatTrans.comp_app]
  exact h.comp (he.precompose E).isFullyFaithful

/-- 元の全 Yoneda の冪等完備化への因子化に沿う制限は、全写像空間で充満忠実。 -/
lemma idemYoneda_pre_isFullyFaithful (C : SSet.{u}) [Quasicategory C]
    (E : SSet.{u + 1}) [Quasicategory E] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda C)).app E) :=
  IsIdempotentCompletion.pre_isFullyFaithful_general (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemYoneda_isIdempotentCompletion C)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
