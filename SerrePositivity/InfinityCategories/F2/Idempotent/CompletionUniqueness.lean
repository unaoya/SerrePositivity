module

public import SerrePositivity.InfinityCategories.F2.Idempotent.UniversalProperty

/-!
概要：元の同じ圏の二つの冪等完備化は、元の二つの包含と全自然同型で整合する同値を持つ。
方針：実際の延長を両向きに構成し、元の制限の充満忠実性で両合成の同型を回収する。
規約：同じ元の二つの包含への比較を保持し、対象だけの一意性で代用しない。
使われ方：HTT 5.1.4.9 の冪等完備化の一意性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 同じ元の圏の二つの冪等完備化は、元の包含への比較を持つ実際の ∞ 圏同値を持つ。 -/
lemma IsIdempotentCompletion.equivalence_unique {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (f : K ⟶ C) (hf : IsIdempotentCompletion f)
    (g : K ⟶ D) (hg : IsIdempotentCompletion g) :
    ∃ e : QCatEquivalence C D, Nonempty (FunctorIso (f ≫ e.hom) g) := by
  obtain ⟨H, ⟨hH⟩⟩ := IsIdempotentCompletion.exists_extension f hf hg.1 g
  obtain ⟨J, ⟨hJ⟩⟩ := IsIdempotentCompletion.exists_extension g hg hf.1 f
  have kC : FunctorIso (f ≫ (H ≫ J)) (f ≫ (𝟙 C)) :=
    functorIsoOfEq ((hH.postcomp J) ≪≫ hJ)
      (Category.assoc _ _ _) (Category.comp_id f).symm
  have kD : FunctorIso (g ≫ (J ≫ H)) (g ≫ (𝟙 D)) :=
    functorIsoOfEq ((hJ.postcomp H) ≪≫ hH)
      (Category.assoc _ _ _) (Category.comp_id g).symm
  have eC : FunctorIso (H ≫ J) (𝟙 C) :=
    (IsIdempotentCompletion.pre_isFullyFaithful_general f hf).preimageVertexIso kC
  have eD : FunctorIso (J ≫ H) (𝟙 D) :=
    (IsIdempotentCompletion.pre_isFullyFaithful_general g hg).preimageVertexIso kD
  exact ⟨⟨H, J, eC, eD⟩, ⟨hH⟩⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
