module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationCutReindex
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  {m n : ℕ} (s : SimplexData R (DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ全実補正和は、I 上単射な添字変更の像の補正和と一致する。 -/
lemma dgModuleAugmentationPrismCorrection_pullback_of_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : Set.InjOn α (I : Set (Fin (m + 1)))) :
    dgModuleAugmentationPrismCorrection R C E F (s.pullback α) (β.comp α) I a b k =
      dgModuleAugmentationPrismCorrection R C E F s β (I.image α) (α a) (α b) k := by
  have haI : a ∈ I := by rw [ha]; exact I.min'_mem _
  have hbI : b ∈ I := by rw [hb]; exact I.max'_mem _
  unfold dgModuleAugmentationPrismCorrection
  rw [← dgModuleAugmentationCutPoints_image α β I a b haI hbI hi]
  let f : Fin (n + 1) →
      GradedHom R ((s.pullback α).obj a).replacement.val
        (F.obj ((s.pullback α).obj b).source) k := fun j ↦
    Index.sign (I.image α) j •
      dgModuleAugmentationHomotopyCut R C E F s (I.image α) (α a) (α b) k j
  have hK : Set.InjOn α
      ((dgModuleAugmentationCutPoints (β.comp α) I a b) : Set (Fin (m + 1))) :=
    hi.mono (Finset.filter_subset _ _)
  change _ = ∑ j ∈ (dgModuleAugmentationCutPoints (β.comp α) I a b).image α, f j
  rw [Finset.sum_image hK]
  dsimp only [f]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := Finset.mem_filter.mp hj
  rw [dgModuleAugmentationHomotopyCut_pullback_of_inj R C E F s α I a b k hI ha hb hk
    hi j hm.1 hm.2.1 hm.2.2.1]
  simp only [Index.sign, Index.image_sign_card α.monotone hi hm.1]
/-- 同じ実混合係数は、I 上単射な添字変更の像の実混合係数と一致する。 -/
lemma dgModuleAugmentationPrismMixedHom_pullback_of_inj
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : Set.InjOn α (I : Set (Fin (m + 1)))) :
    dgModuleAugmentationPrismMixedHom R C E F (s.pullback α) (β.comp α) I a b k
        hI ha hb hk =
      dgModuleAugmentationPrismMixedHom R C E F s β (I.image α) (α a) (α b) k
        (Index.image_two hi hI)
        (Index.image_min α.monotone (by rw [ha]; exact I.isLeast_min' _) _)
        (Index.image_max α.monotone (by rw [hb]; exact I.isGreatest_max' _) _)
        (by rw [Finset.card_image_of_injOn hi]; exact hk) := by
  rw [dgModuleAugmentationPrismMixedHom_eq_base_add_correction,
    dgModuleAugmentationPrismMixedHom_eq_base_add_correction,
    dgModuleAugmentationPrismCorrection_pullback_of_inj R C E F s α β I a b k hI ha hb hk hi,
    SimplexData.pullback_hom_of_inj s α I a b k hI ha hb hk hi]
  rfl
end SerrePositivity.InfinityCategories
