module
public import SerrePositivity.InfinityCategories.DoldKanComparison.StandardComposition

/-! # 閉零元の定数単体との AW 合成

概要：任意の閉零元の定数単体との AW 合成を、元の斉次前後合成として計算する。
方針：最小・最大切断点以外の定数の高次成分を消去する。
規約：任意の元の成分族に成立。使われ方：実 pinched Hom の閉前後合成との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded DGNerve.PinchedHom
open DoldKanComparison
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y z : D}
/-- 後の射が閉定数の AW 合成は、同じ閉元による全成分後合成。 -/
lemma awData_closed_post_component (c : zeroCycles (homObject A D y z)) {n : ℕ}
    (f : LinearData A x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (awData (standardConstant c n).val f).component J k hJ hk =
      compose A c.val (f.component J k hJ hk) (add_zero k) := by
  rw [awData_component, Finset.sum_eq_single (⟨J.min' hJ, J.min'_mem hJ⟩ : J)]
  · unfold awTerm
    apply compose_eq_of_heq _ c.val _ (f.component J k hJ hk)
    · exact standardConstant_component_heq c _ _ _ _ (by rw [AWIndex.left_at_min hJ]; simp)
    · exact component_heq_of_eq f _ _ (AWIndex.right_at_min hJ) _ _ _ hJ rfl hk
    · rw [AWIndex.right_at_min hJ]; exact hk.symm
    · rw [AWIndex.left_at_min hJ]; simp
  · intro j _ hj
    have hne : j.val ≠ J.min' hJ := fun he => hj (Subtype.ext he)
    unfold awTerm
    rw [standardConstant_component_zero _ _ _ _ _ (AWIndex.left_two_of_ne_min hJ j.property hne)]
    exact SerrePositivity.InfinityCategories.DGNerve.zero_compose _ _
  · intro h
    exact (h (Finset.mem_univ _)).elim
/-- 前の射が閉定数の AW 合成は、同じ閉元による全成分前合成。 -/
lemma awData_closed_pre_component (c : zeroCycles (homObject A D x y)) {n : ℕ}
    (g : LinearData A y z n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (awData g (standardConstant c n).val).component J k hJ hk =
      compose A (g.component J k hJ hk) c.val (zero_add k) := by
  rw [awData_component, Finset.sum_eq_single (⟨J.max' hJ, J.max'_mem hJ⟩ : J)]
  · unfold awTerm
    apply compose_eq_of_heq _ (g.component J k hJ hk) _ c.val
    · exact component_heq_of_eq g _ _ (AWIndex.left_at_max hJ) _ _ _ hJ rfl hk
    · exact standardConstant_component_heq c _ _ _ _ (by rw [AWIndex.right_at_max hJ]; simp)
    · rw [AWIndex.right_at_max hJ]; simp
    · rw [AWIndex.left_at_max hJ]; exact hk.symm
  · intro j _ hj
    have hne : j.val ≠ J.max' hJ := fun he => hj (Subtype.ext he)
    unfold awTerm
    rw [standardConstant_component_zero _ _ _ _ _ (AWIndex.right_two_of_ne_max hJ j.property hne)]
    exact SerrePositivity.InfinityCategories.DGNerve.compose_zero _ _
  · intro h
    exact (h (Finset.mem_univ _)).elim

end SerrePositivity.InfinityCategories
