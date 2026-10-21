module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugMixedCuts
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
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
/-- 実切断係数を内部点の二相で、同じ基底・比較差・左右補正へ分ける。 -/
lemma dgCommaAugmentationMixedTransport_cut
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1)
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    dgCommaAugmentationMixedTransport R C E F s β a b (k + 1) hpa hpb
        ((dgCommaAugmentationPrismData R C E F s β).cutCompose I a b k j) =
      (dgCommaAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.cutCompose I a b k j) +
      (if β j = 1 then dgCommaAugmentationCutComparisonBoundary R C E F s I a b k j +
        dgCommaAugmentationImageCorrection R C E F s β I a b k j else
        dgCommaAugmentationSuffixCorrection R C E F s β I a b k j) := by
  by_cases hpj : β j = 1
  · rw [dgCommaAugmentationMixedTransport_cut_one R C E F s β I a b k
      hI ha hb hk hpa hpb j hj haj hjb hpj, ite_eq_left hpj,
      ← dgCommaAugmentationBaseCut_comparison R C E F s I a b k hk j hj, add_assoc]
  · have hv : (β j).val ≠ 1 := by
      intro he
      exact hpj (Fin.ext he)
    have hp0 : β j = 0 := by
      apply Fin.ext
      have := (β j).isLt
      change (β j).val = 0
      omega
    rw [dgCommaAugmentationMixedTransport_cut_zero R C E F s β I a b k
      hI ha hb hk hpa hpb j hj haj hjb hp0, ite_eq_right hpj]
/-- 実混合候補の全二次境界は、基底二次境界・比較差・同じ左右補正の合成和。 -/
lemma dgCommaAugmentationMixedTransport_quadraticBoundary
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) :
    dgCommaAugmentationMixedTransport R C E F s β a b (k + 1) hpa hpb
        ((dgCommaAugmentationPrismData R C E F s β).quadraticBoundary I a b k) =
      (dgCommaAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.quadraticBoundary I a b k) +
      (∑ j ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I j •
        dgCommaAugmentationCutComparisonBoundary R C E F s I a b k j) +
      (∑ j ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I j •
        dgCommaAugmentationImageCorrection R C E F s β I a b k j) +
      (∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
        dgCommaAugmentationSuffixCorrection R C E F s β I a b k j) := by
  simp only [SimplexData.quadraticBoundary, Units.smul_def, map_sum, map_zsmul,
    dgCommaAugmentationCutPoints_eq_filter_interior, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := Finset.mem_filter.mp hj
  rw [dgCommaAugmentationMixedTransport_cut R C E F s β I a b k hI ha hb hk
    hpa hpb j hm.1 hm.2.1 hm.2.2]
  by_cases hpj : β j = 1 <;> simp [hpj, smul_add, add_assoc]
end SerrePositivity.InfinityCategories
