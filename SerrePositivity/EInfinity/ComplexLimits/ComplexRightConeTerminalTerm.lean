module
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeTerminalComposition
public import SerrePositivity.EInfinity.ComplexLimits.ComplexRightConeTerminalZero

/-!
概要：実右 cone の終端を含む全有限集合で、各内部 HA 項は零である。
方針：右切断が二点なら augmentation の全整合式で相殺し、それ以外は高次の零を使う。
規約：元の有限集合・全次数を保持する。使われ方：実右 cone の全 HA 方程式。
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

lemma complexRightConeData_term_last {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : ComplexSimplexAugmentation A s X)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1))
    (j : Fin (n + 2)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    (complexRightConeData A η).term I a b k hI ha hb hk j hj haj hjb = 0 := by
  have ham : IsLeast (I : Set (Fin (n + 2))) a := by rw [ha]; exact I.isLeast_min' _
  have hbm : IsGreatest (I : Set (Fin (n + 2))) b := by rw [hb]; exact I.isGreatest_max' _
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two ham.1 hbm.1 haj hjb
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two ham.1 hj haj
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbm.1 hjb
  have hke : k + 1 = 2 - ((I.erase j).card : ℤ) := by
    have := Finset.card_erase_add_one hj; omega
  by_cases hrc : (I.filter (j ≤ ·)).card = 2
  · have hf := complexRightConeData_hom_last A η (I.erase j) a b (k + 1) he
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min ham haj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max hbm hjb _) hke hbl
    have hc := complexRightConeData_terminal_compose A η I a b k hI ha hb hk hbl j hj haj hjb hrc
    have hp : k + 1 = 2 - ((I.filter (· ≤ j)).card : ℤ) := by
      have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega
    have ht : ∀ l r : ℤ, l = r →
        HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map
          (η.app ((Fin.last n).predAboveOrderHom a))) l)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map
            (η.app ((Fin.last n).predAboveOrderHom a))) r) := by
      intro l r h
      subst r
      rfl
    have hsame := eq_of_heq (hf.trans ((ht _ _ hp).trans hc.symm))
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term]
    rw [hsame, sub_self, smul_zero]
  · have hq : (2 - ((I.filter (j ≤ ·)).card : ℤ)) ≠ 0 := by omega
    have hp : k + 1 ≠ 0 := by have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega
    have hfe := complexRightConeData_hom_last_zero A η (I.erase j) a b (k + 1) he
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min ham haj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max hbm hjb _) hke hbl hp
    have hfr := complexRightConeData_hom_last_zero A η (I.filter (j ≤ ·)) j b _ hr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbm hjb.le _) rfl hbl hq
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term]
    rw [hfe, hfr]
    simp [compose, forward]

end SerrePositivity.EInfinity.ComplexLimits
