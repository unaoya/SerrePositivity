module
public import SerrePositivity.KST.Fibration.CompletedTwoModel
public import SerrePositivity.KST.Fibration.GappedPullback
public import SerrePositivity.KST.SConstruction.STrivialFibration
public import SerrePositivity.KST.SConstruction.ObjectSConstruction

/-! # 補完した二辺図式の元の相対 subobject 上の S 引き戻し -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 補完した二辺の元の第一 W 辺を抽出する完全関手。 -/
def completedTwoFirst {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    completedTwoModel q ⟶ weakArrowModel q :=
  completedTwoForget q ≫ composableWeakFirstExact q

/-- 元の相対 subobject 上で、保持した補完と第一辺は厳密引き戻し。 -/
lemma completedTwo_isPullback {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsPullback (completedTwoCofiber q).val (completedTwoFirst q).val
      (relativeCofiberSubobject (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q)).val (weakArrowTargetTopExact q).val := by
  have h : IsPullback (completedTwoCofiber q).val (completedTwoForget q).val
      (weakArrowCofiberEquivalence q).hom.val (composableWeakNextExact q).val :=
    IsPullback.of_hasPullback _ _
  have ht := (h.flip.paste_horiz (composableWeakArrow_top_isPullback q)).flip
  change IsPullback _ _
    ((weakArrowCofiberEquivalence q).hom ≫ weakArrowSourceTopExact q).val _ at ht
  rw [weakCofiberProjection_sourceTop] at ht
  exact ht

/-- 両保持成分の gapped 性は元の補完した図式の gapped 性を正確に反映する。 -/
lemma completedTwo_isGapped_iff {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : ℕ}
    (F : arNerve n ⟶ (completedTwoModel q).carrier) :
    IsGapped F ↔ IsGapped (F ≫ (completedTwoCofiber q).val) ∧
      IsGapped (F ≫ (completedTwoFirst q).val) := by
  constructor
  · intro h
    exact ⟨h.postcomp _ (stableModelHom_preservesSConstructionData (completedTwoCofiber q)),
      h.postcomp _ (stableModelHom_preservesSConstructionData (completedTwoFirst q))⟩
  · rintro ⟨hc, hf⟩
    apply (isGapped_iff_postcomp_of_trivialKanFibration (completedTwoForget q).val F).2
    apply (composableWeakArrow_isGapped_iff q (F ≫ (completedTwoForget q).val)).2
    refine ⟨?_, ?_⟩
    · exact hf
    · have hn := hc.postcomp _
        (stableModelHom_preservesSConstructionData (weakArrowCofiberEquivalence q).hom)
      change IsGapped (F ≫ (completedTwoCofiber q ≫
        (weakArrowCofiberEquivalence q).hom).val) at hn
      rw [completedTwoCofiber_projection] at hn
      exact hn

/-- 同じ相対 subobject 上の厳密引き戻しを、元の object S 全体でも保持する。 -/
theorem completedTwo_objectS_isPullback {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    IsPullback (objectSConstructionFunctor.map (completedTwoCofiber q))
      (objectSConstructionFunctor.map (completedTwoFirst q))
      (objectSConstructionFunctor.map (relativeCofiberSubobject
        (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q)))
      (objectSConstructionFunctor.map (weakArrowTargetTopExact q)) := by
  apply IsPullback.of_forall_isPullback_app
  intro n
  exact (sConstruction_isPullback_of_gapped_reflection (completedTwo_isPullback q)
    n.unop.len (completedTwo_isGapped_iff q)).map
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌))

end SerrePositivity.KST.Fibration
