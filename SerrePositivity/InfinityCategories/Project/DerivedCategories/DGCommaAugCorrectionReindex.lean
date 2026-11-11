module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommaAugCutReindex
/-!
概要：同じ実切断補正和と混合係数を、添字集合上単射な引き戻しで照合する。
方針：切断点集合の像で総和を移し、同じ各切断係数と右側点数の符号を照合する。
規約：集合外の単射性は要求しない。使われ方：実 augmentation 単体の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
/-- 同じ全実補正和は、I 上単射な添字変更の像の補正和と一致する。 -/
lemma dgCommaAugmentationPrismCorrection_pullback_of_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : Set.InjOn α (I : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCorrection R C E F (s.pullback α) (β.comp α) I a b k =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCorrection R C E F s β (I.image α) (α a) (α b) k := by
  have haI : a ∈ I := by rw [ha]; exact I.min'_mem _
  have hbI : b ∈ I := by rw [hb]; exact I.max'_mem _
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCorrection
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints_image α β I a b haI hbI hi]
  let f : Fin (n + 1) →
      _root_.SerrePositivity.DifferentialGraded.GradedHom R ((s.pullback α).obj a).replacement
        (F.obj ((s.pullback α).obj b).source) k := fun j ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.image α) j •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyCut R C E F s (I.image α) (α a) (α b) k j
  have hK : Set.InjOn α
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints (β.comp α) I a b) : Set (Fin (m + 1))) :=
    hi.mono (Finset.filter_subset _ _)
  change _ = ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints (β.comp α) I a b).image α, f j
  rw [Finset.sum_image hK]
  dsimp only [f]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := Finset.mem_filter.mp hj
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyCut_pullback_of_inj R C E F s α I a b k hI ha hb hk
    hi j hm.1 hm.2.1 hm.2.2.1]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_sign_card α.monotone hi hm.1]
/-- 同じ実混合係数は、I 上単射な添字変更の像の実混合係数と一致する。 -/
lemma dgCommaAugmentationPrismMixedHom_pullback_of_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : Set.InjOn α (I : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R C E F (s.pullback α) (β.comp α) I a b k
        hI ha hb hk =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R C E F s β (I.image α) (α a) (α b) k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hI)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (by rw [ha]; exact I.isLeast_min' _) _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (by rw [hb]; exact I.isGreatest_max' _) _)
        (by rw [Finset.card_image_of_injOn hi]; exact hk) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom_eq_base_add_correction,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom_eq_base_add_correction,
    dgCommaAugmentationPrismCorrection_pullback_of_inj R C E F s α β I a b k hI ha hb hk hi,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj s α I a b k hI ha hb hk hi]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
