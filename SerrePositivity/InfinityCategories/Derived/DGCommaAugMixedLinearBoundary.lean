module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugBaseComparisonCut
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismPhaseCoefficients
/-!
概要：実混合候補の線形境界を、同じ基底と全削除補正へ移す。
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
/-- 同じ混合端点の実 Hom を、元の比較対象と入力像の Hom へ移す線形同型。 -/
def dgCommaAugmentationMixedTransport (β : Fin (n + 1) →o Fin 2)
    (a b : Fin (n + 1)) (k : ℤ) (hpa : β a = 0) (hpb : β b = 1) :
    GradedHom R ((dgCommaAugmentationPrismData R C E F s β).obj a)
      ((dgCommaAugmentationPrismData R C E F s β).obj b) k ≃ₗ[R]
      GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) k :=
  gradedHomTransport (dgCommaAugmentationPrismData_obj_zero R C E F s β a hpa)
    (dgCommaAugmentationPrismData_obj_one R C E F s β b hpb) rfl
/-- 実混合候補の線形境界は、基底線形境界の像と全削除補正の和。 -/
lemma dgCommaAugmentationMixedTransport_linearBoundary
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1) :
    dgCommaAugmentationMixedTransport R C E F s β a b (k + 1) hpa hpb
        ((dgCommaAugmentationPrismData R C E F s β).linearBoundary I a b k) =
      (dgCommaAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.linearBoundary I a b k) +
      ∑ j ∈ Index.interior I a b, Index.sign I j •
        dgCommaAugmentationPrismCorrection R C E F s β (I.erase j) a b (k + 1) := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  simp only [SimplexData.linearBoundary, Units.smul_def, map_sum, map_zsmul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := Finset.mem_filter.mp hj
  have hE := Index.erase_two hamin.1 hbmax.1 hm.2.1 hm.2.2
  have haE := Index.erase_min hamin hm.2.1 (Index.nonempty hE)
  have hbE := Index.erase_max hbmax hm.2.2 (Index.nonempty hE)
  have hkE : k + 1 = 2 - ((I.erase j).card : ℤ) := by
    have := Finset.card_erase_add_one hm.1
    omega
  have he := gradedHomTransport_eq_of_heq
    (dgCommaAugmentationPrismData_obj_zero R C E F s β a hpa)
    (dgCommaAugmentationPrismData_obj_one R C E F s β b hpb) (rfl : k + 1 = k + 1)
    ((dgCommaAugmentationPrismData R C E F s β).homOrZero (I.erase j) a b (k + 1))
    (dgCommaAugmentationPrismMixedHom R C E F s β (I.erase j) a b (k + 1)
      hE haE hbE hkE)
    (dgCommaAugmentationPrismData_homOrZero_mixed R C E F s β (I.erase j) a b (k + 1)
      hE haE hbE hkE hpa hpb)
  change dgCommaAugmentationMixedTransport R C E F s β a b (k + 1) hpa hpb
    ((dgCommaAugmentationPrismData R C E F s β).homOrZero (I.erase j) a b (k + 1)) = _ at he
  rw [he, dgCommaAugmentationPrismMixedHom_eq_base_add_correction,
    SimplexData.homOrZero_eq s (I.erase j) a b (k + 1) hE haE hbE hkE,
    dgCommaAugmentationBaseHomMap_apply]
  exact smul_add _ _ _
end SerrePositivity.InfinityCategories
