module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionRestrictionImage

/-!
概要：元の任意の冪等完備化に沿って、冪等完備な標的への全関手を延長する。
方針：元の頂点像へ因子化し、全部分圏上の構成済みの延長を元の全関手へ戻す。
規約：元の射の単射性・inner 性を仮定せず、元の制限の全自然同型を結論する。
使われ方：HTT 5.1.4.8〜9 の元の制限関手の本質的全射性。

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

/-- 元の任意の冪等完備化に沿って、冪等完備な元の標的へ全関手を延長する。 -/
lemma IsIdempotentCompletion.exists_extension {K C E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory E]
    (δ : K ⟶ C) (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion δ) (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete E)
    (F : K ⟶ E) : ∃ H : C ⟶ E, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (δ ≫ H) F) := by
  let P := fun y ↦ ∃ x, δ.app (Opposite.op ⦋0⦌) x = y
  let i := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C P).ι
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.fullSubcomplexVertexImageLift_isQCatEquivalence δ hδ.2.1).choose
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.vertexImage δ hδ
  have hfac : e.hom ≫ i = δ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι P δ (fun x ↦ ⟨x, rfl⟩)
  obtain ⟨H, ⟨hH⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.exists_extension_to_complete_of_full_inclusion i hi hE (e.inv ≫ F)
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (δ ≫ H) ((e.hom ≫ e.inv) ≫ F) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (hH.precomp e.hom)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ H) hfac))
      (Category.assoc _ _ _).symm
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((e.hom ≫ e.inv) ≫ F) F := by
    simpa only [Category.id_comp] using e.homInvIso.postcomp F
  exact ⟨H, ⟨h₀ ≪≫ h₁⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
