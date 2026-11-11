module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornResidual

/-! # 真部分集合の方程式と右辺の閉性

概要：真部分集合で全ての方程式が成り立つとき、その集合の方程式の右辺は閉じている。
方針：Bianchi 恒等式の削除集合と左右切断は真部分集合なので、その残差を消去する。
規約：HA Proposition 1.3.1.10。使われ方：N7c の先頭の未知成分の右辺の閉性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：全ての真部分集合の方程式を満たすデータの右辺は閉じている。
方針：主残差恒等式における削除集合と左右切断の残差を真部分集合の方程式で零にする。
規約：HA Proposition 1.3.1.10。使われ方：先頭の未知成分の閉じた障害成分の計算。 -/
lemma differential_rhs_zero_of_proper_equations {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (hproper : ∀ J ⊂ I, s.Equation J)
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    differential A (s.rhs I a b k hI ha hb hk) = 0 := by
  rw [s.bianchi]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hint : a < j.val ∧ j.val < b
  · rw [dite_eq_left hint]
    have haMem : a ∈ I := ha ▸ I.min'_mem _
    have hbMem : b ∈ I := hb ▸ I.max'_mem _
    have hL : I.filter (· ≤ j.val) ⊂ I := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro he
      have hm : b ∈ I.filter (· ≤ j.val) := he.symm ▸ hbMem
      exact not_le_of_gt hint.2 (Finset.mem_filter.mp hm).2
    have hR : I.filter (j.val ≤ ·) ⊂ I := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro he
      have hm : a ∈ I.filter (j.val ≤ ·) := he.symm ▸ haMem
      exact not_le_of_gt hint.1 (Finset.mem_filter.mp hm).2
    rw [s.residualContribution_of_cuts I a b k hI ha hb hk j.val j.property hint.1 hint.2
      (hproper _ hL) (hproper _ hR),
      s.residual_zero_of_equation _ (hproper _ (Finset.erase_ssubset j.property)), smul_zero]
  · simp only [dite_eq_right hint]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (differential_rhs_zero_of_proper_equations)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
