module
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeNaturality
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeClosed

/-!
概要：終端の二点右切断の実合成は、指定 augmentation の同じ始点成分に一致する。
方針：右辺を閉 augmentation、左辺を元の単体へ戻して全斉次整合式を適用する。
規約：同じ実切断と次数を保持する。使われ方：終端 HA の内部項の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma complexRightConeData_terminal_compose {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : ComplexSimplexAugmentation A s X)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1))
    (j : Fin (n + 2)) (hj : j ∈ I) (haj : a < j) (hjb : j < b)
    (hrc : (I.filter (j ≤ ·)).card = 2) :
    HEq (compose A
      ((complexRightConeData A η).hom (I.filter (j ≤ ·)) j b
        (2 - ((I.filter (j ≤ ·)).card : ℤ))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj (by rw [hb]; exact I.max'_mem _) hjb)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max (by rw [hb]; exact I.isGreatest_max' _) hjb.le _)
        rfl)
      ((complexRightConeData A η).hom (I.filter (· ≤ j)) a j
        (2 - ((I.filter (· ≤ j)).card : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two (by rw [ha]; exact I.min'_mem _) hj haj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min (by rw [ha]; exact I.isLeast_min' _) haj.le _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl)
      (show (2 - ((I.filter (· ≤ j)).card : ℤ)) +
        (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 by
          have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map (η.app ((Fin.last n).predAboveOrderHom a)))
        (2 - ((I.filter (· ≤ j)).card : ℤ))) := by
  have haI : a ∈ I := by rw [ha]; exact I.min'_mem _
  have hbI : b ∈ I := by rw [hb]; exact I.max'_mem _
  have han : a ≠ Fin.last (n + 1) := by rw [ha]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last I hI
  have hjn : j ≠ Fin.last (n + 1) := by rw [← hbl]; exact hjb.ne
  have hx := complexRightConeObj_ne_last A s X a han
  have hy := complexRightConeObj_ne_last A s X j hjn
  have hz : (complexRightConeData A η).obj b = X := by
    change complexRightConeObj A s X b = X
    rw [hbl, complexRightConeObj_last]
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two haI hj haj
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbI hjb
  have ham : IsLeast (I : Set (Fin (n + 2))) a := by rw [ha]; exact I.isLeast_min' _
  have hbm : IsGreatest (I : Set (Fin (n + 2))) b := by rw [hb]; exact I.isGreatest_max' _
  have he := complexRightConeData_hom_ordinary A η (I.filter (· ≤ j)) a j _ hl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ham haj.le _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl hjn
  have hf := complexRightConeData_hom_last A η (I.filter (j ≤ ·)) j b _ hr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbm hjb.le _) rfl hbl
  have hq : (2 - ((I.filter (j ≤ ·)).card : ℤ)) = 0 := by omega
  have hp : k + 1 = 2 - ((I.filter (· ≤ j)).card : ℤ) := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega
  have hg : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map
      (η.app ((Fin.last n).predAboveOrderHom j))) (2 - ((I.filter (j ≤ ·)).card : ℤ)))
      (ComplexSimplexAugmentation.cycle A η ((Fin.last n).predAboveOrderHom j)).val := by
    rw [hq, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero]
    rfl
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := A) hx hy hz rfl hq hp _ _ _ _ (hf.trans hg) he
    (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega) (add_zero _)
  exact hc.trans (heq_of_eq (complexRightConeData_front_compose A η (I.filter (· ≤ j))
    a j _ hl (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ham haj.le _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl hjn))

end SerrePositivity.EInfinity.ComplexLimits
