module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinearResidual

/-! # Pinched Hom の境界データの閉性

概要：全ての真部分集合で削除方程式を満たす線形データの右辺は閉じている。
方針：右辺の微分を一段小さい残差の和にし、境界の方程式で消す。
規約：最上位の方程式は仮定しない。使われ方：β3 の全境界の充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 一点を消した集合は全体集合ではない。 -/
lemma pinched_erase_ne_univ {n : ℕ} (J : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    J.erase j ≠ Finset.univ := by
  intro h
  have hj : j ∈ J.erase j := h.symm ▸ Finset.mem_univ j
  exact Finset.notMem_erase j J hj

/-- 真部分集合で一致するデータの線形右辺は一致する。 -/
lemma pinched_rhs_eq_of_proper_components {n : ℕ} (f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (he : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      f.component J k hJ hk = g.component J k hJ hk)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    f.rhs J k hk = g.rhs J k hk := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs
  split_ifs with hJ
  · apply Finset.sum_congr rfl
    intro j _
    rw [he _ _ _ _ (pinched_erase_ne_univ J j.val)]
  · rfl

/-- 真部分集合の方程式から、削除方程式の全右辺は閉元になる。 -/
lemma pinched_rhs_closed_of_proper_equations {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (he : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      _root_.SerrePositivity.DifferentialGraded.differential A (f.component J k hJ hk) = f.rhs J k hk)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.DifferentialGraded.differential A (f.rhs J k hk) = 0 := by
  by_cases hJ : 2 ≤ J.card
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.differential_rhs_residual f J k hJ hk]
    apply Finset.sum_eq_zero
    intro j _
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.residual_eq_zero_iff f _ _ _ _).2
      (he _ _ _ _ (pinched_erase_ne_univ J j.val)), smul_zero]
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs, dite_eq_right hJ]
    change (_root_.SerrePositivity.DifferentialGraded.homObject A D x y).d (k + 1) (k + 1 + 1) 0 = 0
    exact map_zero _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
