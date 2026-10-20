module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationMixedLinearBoundary
/-!
概要：実混合候補の各切断合成を、内部点の二相で照合する。
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
/-- 相一で切る実混合係数は、同じ像基底係数と左補正の後合成の和。 -/
lemma dgModuleAugmentationMixedTransport_cut_one
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1)
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) (hpj : β j = 1) :
    dgModuleAugmentationMixedTransport R C E F s β a b (k + 1) hpa hpb
        ((dgModuleAugmentationPrismData R C E F s β).cutCompose I a b k j) =
      dgModuleAugmentationImageBaseCut R C E F s I a b k j +
      dgModuleAugmentationImageCorrection R C E F s β I a b k j := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hL := Index.left_two hamin.1 hj haj
  have hR := Index.right_two hj hbmax.1 hjb
  have haL := Index.left_min hamin haj.le (Index.nonempty hL)
  have hjL := Index.left_max hj (Index.nonempty hL)
  have hjR := Index.right_min hj (Index.nonempty hR)
  have hbR := Index.right_max hbmax hjb.le (Index.nonempty hR)
  have hx := dgModuleAugmentationPrismData_obj_zero R C E F s β a hpa
  have hy := dgModuleAugmentationPrismData_obj_one R C E F s β j hpj
  have hz := dgModuleAugmentationPrismData_obj_one R C E F s β b hpb
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := Index.split_card hj
    omega
  have hcR := gradedHomTransport_eq_of_heq hy hz rfl
    ((dgModuleAugmentationPrismData R C E F s β).homOrZero (I.filter (j ≤ ·)) j b _)
    (((dgModuleAugmentationTarget R C E F).map (s.obj j) (s.obj b)).f _
      (s.hom (I.filter (j ≤ ·)) j b _ hR hjR hbR rfl))
    (dgModuleAugmentationPrismData_homOrZero_one R C E F s β (I.filter (j ≤ ·)) j b _
      hR hjR hbR rfl hpj hpb)
  have hcL := gradedHomTransport_eq_of_heq hx hy rfl
    ((dgModuleAugmentationPrismData R C E F s β).homOrZero (I.filter (· ≤ j)) a j _)
    (dgModuleAugmentationPrismMixedHom R C E F s β (I.filter (· ≤ j)) a j _ hL haL hjL rfl)
    (dgModuleAugmentationPrismData_homOrZero_mixed R C E F s β (I.filter (· ≤ j)) a j _
      hL haL hjL rfl hpa hpj)
  dsimp only [dgModuleAugmentationMixedTransport]
  rw [SimplexData.cutCompose, dite_eq_left hsum,
    gradedHomTransport_compose hx hy hz rfl rfl rfl, hcR, hcL,
    dgModuleAugmentationPrismMixedHom_eq_base_add_correction, compose_add_right]
  rw [dgModuleAugmentationImageBaseCut, dgModuleAugmentationImageCorrection,
    dite_eq_left hsum, dite_eq_left hsum, dgModuleAugmentationBaseHomMap_apply,
    SimplexData.homOrZero_eq s _ _ _ _ hL haL hjL rfl,
    SimplexData.homOrZero_eq s _ _ _ _ hR hjR hbR rfl]
  rfl
/-- 同じ基底切断合成は、右基底係数と左入力像の合成。 -/
lemma dgModuleAugmentationBaseCut_source_assoc
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ I) :
    (dgModuleAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.cutCompose I a b k j) =
      compose R (x := (s.obj a).replacement.val) (y := (s.obj j).replacement.val)
        (z := F.obj (s.obj b).source) (n := k + 1)
        ((dgModuleAugmentationBaseHomMap R C E F (s.obj j) (s.obj b)).f _
          (s.homOrZero (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ))))
        (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
          (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ))))
        (by have := Index.split_card hj; omega) := by
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := Index.split_card hj
    omega
  rw [SimplexData.cutCompose, dite_eq_left hsum,
    dgModuleAugmentationBaseHomMap_apply, dgModuleAugmentationBaseHomMap_apply, map_compose]
  exact compose_assoc_of_sum (A := R) (D := RightModule R E)
    (w := (s.obj a).replacement.val) (x := (s.obj j).replacement.val)
    (y := (s.obj b).replacement.val) (z := F.obj (s.obj b).source)
    (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
      (s.homOrZero (I.filter (· ≤ j)) a j _))
    (((dgModuleAugmentationSource R C E F).map (s.obj j) (s.obj b)).f _
      (s.homOrZero (I.filter (j ≤ ·)) j b _))
    (dgModuleAugmentationComponent R C E F (s.obj b)).val hsum (add_zero _) (add_zero _)
/-- 相零で切る実混合係数は、同じ基底切断合成と右補正の前合成の和。 -/
lemma dgModuleAugmentationMixedTransport_cut_zero
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1)
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) (hpj : β j = 0) :
    dgModuleAugmentationMixedTransport R C E F s β a b (k + 1) hpa hpb
        ((dgModuleAugmentationPrismData R C E F s β).cutCompose I a b k j) =
      (dgModuleAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.cutCompose I a b k j) +
      dgModuleAugmentationSuffixCorrection R C E F s β I a b k j := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hL := Index.left_two hamin.1 hj haj
  have hR := Index.right_two hj hbmax.1 hjb
  have haL := Index.left_min hamin haj.le (Index.nonempty hL)
  have hjL := Index.left_max hj (Index.nonempty hL)
  have hjR := Index.right_min hj (Index.nonempty hR)
  have hbR := Index.right_max hbmax hjb.le (Index.nonempty hR)
  have hx := dgModuleAugmentationPrismData_obj_zero R C E F s β a hpa
  have hy := dgModuleAugmentationPrismData_obj_zero R C E F s β j hpj
  have hz := dgModuleAugmentationPrismData_obj_one R C E F s β b hpb
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := Index.split_card hj
    omega
  have hcR := gradedHomTransport_eq_of_heq hy hz rfl
    ((dgModuleAugmentationPrismData R C E F s β).homOrZero (I.filter (j ≤ ·)) j b _)
    (dgModuleAugmentationPrismMixedHom R C E F s β (I.filter (j ≤ ·)) j b _ hR hjR hbR rfl)
    (dgModuleAugmentationPrismData_homOrZero_mixed R C E F s β (I.filter (j ≤ ·)) j b _
      hR hjR hbR rfl hpj hpb)
  have hcL := gradedHomTransport_eq_of_heq hx hy rfl
    ((dgModuleAugmentationPrismData R C E F s β).homOrZero (I.filter (· ≤ j)) a j _)
    (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
      (s.hom (I.filter (· ≤ j)) a j _ hL haL hjL rfl))
    (dgModuleAugmentationPrismData_homOrZero_zero R C E F s β (I.filter (· ≤ j)) a j _
      hL haL hjL rfl hpa hpj)
  dsimp only [dgModuleAugmentationMixedTransport]
  rw [SimplexData.cutCompose, dite_eq_left hsum,
    gradedHomTransport_compose hx hy hz rfl rfl rfl, hcR, hcL,
    dgModuleAugmentationPrismMixedHom_eq_base_add_correction, compose_add_left]
  rw [dgModuleAugmentationBaseCut_source_assoc R C E F s I a b k hk j hj,
    dgModuleAugmentationSuffixCorrection, dite_eq_left hsum,
    dgModuleAugmentationBaseHomMap_apply,
    SimplexData.homOrZero_eq s _ _ _ _ hL haL hjL rfl,
    SimplexData.homOrZero_eq s _ _ _ _ hR hjR hbR rfl]
end SerrePositivity.InfinityCategories
