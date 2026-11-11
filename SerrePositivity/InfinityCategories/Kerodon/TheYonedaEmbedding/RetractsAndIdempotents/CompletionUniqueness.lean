module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.UniversalProperty

/-!
概要：元の同じ圏の二つの冪等完備化は、元の二つの包含と全自然同型で整合する同値を持つ。
方針：実際の延長を両向きに構成し、元の制限の充満忠実性で両合成の同型を回収する。
規約：同じ元の二つの包含への比較を保持し、対象だけの一意性で代用しない。
使われ方：HTT 5.1.4.9 の冪等完備化の一意性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 同じ元の圏の二つの冪等完備化は、元の包含への比較を持つ実際の ∞ 圏同値を持つ。 -/
lemma IsIdempotentCompletion.equivalence_unique {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (f : K ⟶ C) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f)
    (g : K ⟶ D) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion g) :
    ∃ e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C D, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ e.hom) g) := by
  obtain ⟨H, ⟨hH⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.exists_extension f hf hg.1 g
  obtain ⟨J, ⟨hJ⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.exists_extension g hg hf.1 f
  have kC : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ (H ≫ J)) (f ≫ (𝟙 C)) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((hH.postcomp J) ≪≫ hJ)
      (Category.assoc _ _ _) (Category.comp_id f).symm
  have kD : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ (J ≫ H)) (g ≫ (𝟙 D)) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((hJ.postcomp H) ≪≫ hH)
      (Category.assoc _ _ _) (Category.comp_id g).symm
  have eC : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (H ≫ J) (𝟙 C) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isFullyFaithful_general f hf).preimageVertexIso kC
  have eD : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (J ≫ H) (𝟙 D) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.pre_isFullyFaithful_general g hg).preimageVertexIso kD
  exact ⟨⟨H, J, eC, eD⟩, ⟨hH⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
