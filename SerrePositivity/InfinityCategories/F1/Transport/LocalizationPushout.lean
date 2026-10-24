module

public import SerrePositivity.InfinityCategories.F1.Simplicial.ReplacementSpanComparison

/-!
概要：単射に沿う pushout による、初頂点写像の局所化普遍性の貼り合わせ。
方針：三対象の比較を同時解像し、二つの実際の pullback の同型で元の比較を回収する。
規約：反対側の貼付写像や底の quasicategory 性は仮定しない。
使われ方：標準単体上の局所化から一般の底上の coherent な降下へ進むセル付加。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 単射に沿う pushout の三頂点で初頂点写像が局所化なら、第四頂点でも局所化。 -/
lemma transportSimplexFirstVertexMap_isLocalization_of_isPushout {A B C D : SSet.{u}}
    {i : A ⟶ B} [Mono i] {g : A ⟶ C} {k : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout i g k j)
    (hA : IsLocalization (transportSimplexFirstVertexMap A) (transportSimplexInitialEdges A))
    (hB : IsLocalization (transportSimplexFirstVertexMap B) (transportSimplexInitialEdges B))
    (hC : IsLocalization (transportSimplexFirstVertexMap C) (transportSimplexInitialEdges C)) :
    IsLocalization (transportSimplexFirstVertexMap D) (transportSimplexInitialEdges D) := by
  refine ⟨transportSimplexFirstVertexMap_inverts D, fun E _ ↦ ?_⟩
  let L (Z : SSet.{u}) := localizationPrecomposition (transportSimplexFirstVertexMap Z)
    (transportSimplexInitialEdges Z) (transportSimplexFirstVertexMap_inverts Z) E
  have hL (Z : SSet.{u})
      (hz : IsLocalization (transportSimplexFirstVertexMap Z) (transportSimplexInitialEdges Z)) :
      IsQCatEquivalence (L Z) := by
    obtain ⟨_, hz⟩ := hz
    exact hz E
  have h₁ : L B ≫ transportSimplexInvertingRestriction i E = (pre i).app E ≫ L A :=
    (transportSimplexLocalizationPrecomposition_naturality i E).symm
  have h₂ : L C ≫ transportSimplexInvertingRestriction g E = (pre g).app E ≫ L A :=
    (transportSimplexLocalizationPrecomposition_naturality g E).symm
  let m := spanPullbackMap ((pre i).app E) ((pre g).app E)
    (transportSimplexInvertingRestriction i E) (transportSimplexInvertingRestriction g E)
    (L A) (L B) (L C) h₁ h₂
  have hm : IsPrecompositionEquivalence m :=
    isPrecompositionEquivalence_spanPullbackMap_of_equivalenceLifting
      ((pre i).app E) ((pre g).app E) (transportSimplexInvertingRestriction i E)
      (transportSimplexInvertingRestriction g E) (L A) (L B) (L C) h₁ h₂
      (hL A hA) (hL B hB) (hL C hC) (SerrePositivity.InfinityCategories.F1B.equivalenceLifting_pre i)
      (kanEquivalenceLifting_transportSimplexInvertingRestriction i E)
  have hs := (isPullback_pre_of_isPushout h E).flip
  have ht := (transportSimplexInverting_isPullback_of_isPushout h E).flip
  let es := hs.isoPullback
  let et := ht.isoPullback
  have hsf : es.hom ≫ pullback.fst ((pre i).app E) ((pre g).app E) = (pre k).app E :=
    hs.isoPullback_hom_fst
  have hss : es.hom ≫ pullback.snd ((pre i).app E) ((pre g).app E) = (pre j).app E :=
    hs.isoPullback_hom_snd
  have htf : et.hom ≫ pullback.fst (transportSimplexInvertingRestriction i E)
      (transportSimplexInvertingRestriction g E) = transportSimplexInvertingRestriction k E :=
    ht.isoPullback_hom_fst
  have hts : et.hom ≫ pullback.snd (transportSimplexInvertingRestriction i E)
      (transportSimplexInvertingRestriction g E) = transportSimplexInvertingRestriction j E :=
    ht.isoPullback_hom_snd
  have hc : L D ≫ et.hom = es.hom ≫ m := by
    apply pullback.hom_ext
    · rw [Category.assoc, htf, Category.assoc]
      change L D ≫ transportSimplexInvertingRestriction k E =
        es.hom ≫ (spanPullbackMap _ _ _ _ _ _ _ h₁ h₂ ≫ pullback.fst _ _)
      rw [spanPullbackMap_fst, ← Category.assoc, hsf]
      exact (transportSimplexLocalizationPrecomposition_naturality k E).symm
    · rw [Category.assoc, hts, Category.assoc]
      change L D ≫ transportSimplexInvertingRestriction j E =
        es.hom ≫ (spanPullbackMap _ _ _ _ _ _ _ h₁ h₂ ≫ pullback.snd _ _)
      rw [spanPullbackMap_snd, ← Category.assoc, hss]
      exact (transportSimplexLocalizationPrecomposition_naturality j E).symm
  have hd : L D = es.hom ≫ m ≫ et.inv := by
    apply (cancel_mono et.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hc
  change IsQCatEquivalence (L D)
  rw [hd]
  exact (qCatEquivalenceOfIso es).isQCatEquivalence.comp
    (hm.isQCatEquivalence.comp (qCatEquivalenceOfIso et.symm).isQCatEquivalence)

end SerrePositivity.InfinityCategories
