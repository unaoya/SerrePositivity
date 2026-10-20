module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationMixedCuts
/-!
概要：実混合候補の二次境界を、同じ基底・比較差・左右補正へ移す。
方針：相別係数の回収と Hom の線形移送、既証明の実微分式を使う。
規約：単体作用の自然性は別工程。使われ方：全 augmentation prism の単体構成。
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
  {n : ℕ} (s : SimplexData R (DGModuleFunctorResolutionObject R C E F) n)
/-- 実切断係数を内部点の二相で、同じ基底・比較差・左右補正へ分ける。 -/
lemma dgModuleAugmentationMixedTransport_cut
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1)
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    dgModuleAugmentationMixedTransport R C E F s β a b (k + 1) hpa hpb
        ((dgModuleAugmentationPrismData R C E F s β).cutCompose I a b k j) =
      (dgModuleAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.cutCompose I a b k j) +
      (if β j = 1 then dgModuleAugmentationCutComparisonBoundary R C E F s I a b k j +
        dgModuleAugmentationImageCorrection R C E F s β I a b k j else
        dgModuleAugmentationSuffixCorrection R C E F s β I a b k j) := by
  by_cases hpj : β j = 1
  · rw [dgModuleAugmentationMixedTransport_cut_one R C E F s β I a b k
      hI ha hb hk hpa hpb j hj haj hjb hpj, ite_eq_left hpj,
      ← dgModuleAugmentationBaseCut_comparison R C E F s I a b k hk j hj, add_assoc]
  · have hv : (β j).val ≠ 1 := by
      intro he
      exact hpj (Fin.ext he)
    have hp0 : β j = 0 := by
      apply Fin.ext
      have := (β j).isLt
      change (β j).val = 0
      omega
    rw [dgModuleAugmentationMixedTransport_cut_zero R C E F s β I a b k
      hI ha hb hk hpa hpb j hj haj hjb hp0, ite_eq_right hpj]
/-- 実混合候補の全二次境界は、基底二次境界・比較差・同じ左右補正の合成和。 -/
lemma dgModuleAugmentationMixedTransport_quadraticBoundary
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) :
    dgModuleAugmentationMixedTransport R C E F s β a b (k + 1) hpa hpb
        ((dgModuleAugmentationPrismData R C E F s β).quadraticBoundary I a b k) =
      (dgModuleAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.quadraticBoundary I a b k) +
      (∑ j ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I j •
        dgModuleAugmentationCutComparisonBoundary R C E F s I a b k j) +
      (∑ j ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I j •
        dgModuleAugmentationImageCorrection R C E F s β I a b k j) +
      (∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
        dgModuleAugmentationSuffixCorrection R C E F s β I a b k j) := by
  simp only [SimplexData.quadraticBoundary, Units.smul_def, map_sum, map_zsmul,
    dgModuleAugmentationCutPoints_eq_filter_interior, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := Finset.mem_filter.mp hj
  rw [dgModuleAugmentationMixedTransport_cut R C E F s β I a b k hI ha hb hk
    hpa hpb j hm.1 hm.2.1 hm.2.2]
  by_cases hpj : β j = 1 <;> simp [hpj, smul_add, add_assoc]
end SerrePositivity.InfinityCategories
