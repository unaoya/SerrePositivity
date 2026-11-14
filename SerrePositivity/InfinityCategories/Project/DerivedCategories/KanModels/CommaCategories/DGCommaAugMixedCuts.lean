module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugMixedLinearBoundary
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
/-- 相一で切る実混合係数は、同じ像基底係数と左補正の後合成の和。 -/
lemma dgCommaAugmentationMixedTransport_cut_one
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1)
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) (hpj : β j = 1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationMixedTransport R C E F s β a b (k + 1) hpa hpb
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s β).cutCompose I a b k j) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationImageBaseCut R C E F s I a b k j +
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationImageCorrection R C E F s β I a b k j := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two hamin.1 hj haj
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbmax.1 hjb
  have haL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min hamin haj.le (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL)
  have hjL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL)
  have hjR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR)
  have hbR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbmax hjb.le (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR)
  have hx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_zero R C E F s β a hpa
  have hy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_one R C E F s β j hpj
  have hz := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_one R C E F s β b hpb
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  have hcR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_eq_of_heq hy hz rfl
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s β).homOrZero (I.filter (j ≤ ·)) j b _)
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R C E F).map (s.obj j) (s.obj b)).f _
      (s.hom (I.filter (j ≤ ·)) j b _ hR hjR hbR rfl))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_homOrZero_one R C E F s β (I.filter (j ≤ ·)) j b _
      hR hjR hbR rfl hpj hpb)
  have hcL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_eq_of_heq hx hy rfl
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s β).homOrZero (I.filter (· ≤ j)) a j _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R C E F s β (I.filter (· ≤ j)) a j _ hL haL hjL rfl)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_homOrZero_mixed R C E F s β (I.filter (· ≤ j)) a j _
      hL haL hjL rfl hpa hpj)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationMixedTransport]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose, dite_eq_left hsum,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_compose hx hy hz rfl rfl rfl, hcR, hcL,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom_eq_base_add_correction, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_right]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationImageBaseCut, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationImageCorrection,
    dite_eq_left hsum, dite_eq_left hsum, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationBaseHomMap_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s _ _ _ _ hL haL hjL rfl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s _ _ _ _ hR hjR hbR rfl]
  rfl
/-- 同じ基底切断合成は、右基底係数と左入力像の合成。 -/
lemma dgCommaAugmentationBaseCut_source_assoc
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ I) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.cutCompose I a b k j) =
      _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement) (y := (s.obj j).replacement)
        (z := F.obj (s.obj b).source) (n := k + 1)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationBaseHomMap R C E F (s.obj j) (s.obj b)).f _
          (s.homOrZero (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ))))
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
          (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ))))
        (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega) := by
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose, dite_eq_left hsum,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationBaseHomMap_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationBaseHomMap_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := R) (D := E)
    (w := (s.obj a).replacement) (x := (s.obj j).replacement)
    (y := (s.obj b).replacement) (z := F.obj (s.obj b).source)
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
      (s.homOrZero (I.filter (· ≤ j)) a j _))
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj j) (s.obj b)).f _
      (s.homOrZero (I.filter (j ≤ ·)) j b _))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R C E F (s.obj b)).val hsum (add_zero _) (add_zero _)
/-- 相零で切る実混合係数は、同じ基底切断合成と右補正の前合成の和。 -/
lemma dgCommaAugmentationMixedTransport_cut_zero
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = 0) (hpb : β b = 1)
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) (hpj : β j = 0) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationMixedTransport R C E F s β a b (k + 1) hpa hpb
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s β).cutCompose I a b k j) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.cutCompose I a b k j) +
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSuffixCorrection R C E F s β I a b k j := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two hamin.1 hj haj
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbmax.1 hjb
  have haL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min hamin haj.le (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL)
  have hjL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL)
  have hjR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR)
  have hbR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbmax hjb.le (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR)
  have hx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_zero R C E F s β a hpa
  have hy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_zero R C E F s β j hpj
  have hz := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_obj_one R C E F s β b hpb
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  have hcR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_eq_of_heq hy hz rfl
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s β).homOrZero (I.filter (j ≤ ·)) j b _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R C E F s β (I.filter (j ≤ ·)) j b _ hR hjR hbR rfl)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_homOrZero_mixed R C E F s β (I.filter (j ≤ ·)) j b _
      hR hjR hbR rfl hpj hpb)
  have hcL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_eq_of_heq hx hy rfl
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData R C E F s β).homOrZero (I.filter (· ≤ j)) a j _)
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
      (s.hom (I.filter (· ≤ j)) a j _ hL haL hjL rfl))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_homOrZero_zero R C E F s β (I.filter (· ≤ j)) a j _
      hL haL hjL rfl hpa hpj)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationMixedTransport]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose, dite_eq_left hsum,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_compose hx hy hz rfl rfl rfl, hcR, hcL,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom_eq_base_add_correction, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left]
  rw [dgCommaAugmentationBaseCut_source_assoc R C E F s I a b k hk j hj,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSuffixCorrection, dite_eq_left hsum,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationBaseHomMap_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s _ _ _ _ hL haL hjL rfl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s _ _ _ _ hR hjR hbR rfl]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
