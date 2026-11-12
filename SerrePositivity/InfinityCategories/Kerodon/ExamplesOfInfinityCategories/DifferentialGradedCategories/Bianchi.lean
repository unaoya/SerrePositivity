module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubicBoundary

/-! # dg nerve の主残差恒等式

概要：方程式の右辺を微分すると、真部分集合の残差だけを含む和になる。
方針：純代数寄与を二重削除・混合・三重合成に分け、証明済みの三つの相殺を適用する。
規約：HA Proposition 1.3.1.10。使われ方：内部ホーンの欠けた面の方程式の検証。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：純代数寄与は二重削除・混合・三重合成の各項に分かれる。
方針：真部分集合の右辺を線形部分と合成部分に分け、合成を差へ分配する。
規約：HA Proposition 1.3.1.10。使われ方：三つの相殺を元の寄与に接続する。 -/
lemma rhsContribution_eq_boundaries {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    s.rhsContribution I a b k hI ha hb hk j hj haj hjb = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      (s.linearBoundary (I.erase j) a b (k + 1) - s.quadraticBoundary (I.erase j) a b (k + 1) -
        s.cutBoundary s.linearBoundary I a b k j +
        s.cutBoundary s.quadraticBoundary I a b k j) := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by rw [hb]; exact I.isGreatest_max' _
  have hL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two hamin.1 hj haj
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbmax.1 hjb
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhsContribution, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_eq_linear_sub_quadratic, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.cutBoundary, dite_eq_left hsum]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s _ _ _ _ hL (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min hamin haj.le _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s _ _ _ _ hR (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbmax hjb.le _) rfl]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right, smul_sub, smul_add]
  abel

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (rhsContribution_eq_boundaries)


/-- 概要：単体データの純代数寄与の総和は零。
方針：共通の内部点集合上で二重削除・混合・三重合成の三つの相殺を適用する。
規約：HA Proposition 1.3.1.10。使われ方：残差展開から主残差恒等式を得る。 -/
lemma sum_rhsContribution_eq_zero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (∑ j : I, if h : a < j.val ∧ j.val < b then
      s.rhsContribution I a b k hI ha hb hk j.val j.property h.1 h.2 else 0) = 0 := by
  have heq :
      (∑ j : I, if h : a < j.val ∧ j.val < b then
        s.rhsContribution I a b k hI ha hb hk j.val j.property h.1 h.2 else 0) =
      ∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        (s.linearBoundary (I.erase j) a b (k + 1) - s.quadraticBoundary (I.erase j) a b (k + 1) -
          s.cutBoundary s.linearBoundary I a b k j +
          s.cutBoundary s.quadraticBoundary I a b k j) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior, Finset.sum_filter, ← Finset.sum_coe_sort I]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hint : a < j.val ∧ j.val < b
    · simp only [dite_eq_left hint, ite_eq_left hint]
      exact rhsContribution_eq_boundaries s I a b k hI ha hb hk j.val j.property hint.1 hint.2
    · simp only [dite_eq_right hint, ite_eq_right hint]
  rw [heq]
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.linearBoundary_squared, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubicBoundary_eq_zero s I a b k hk]
  simpa only [zero_sub, sub_eq_add_neg, add_zero, zero_add, neg_add, neg_zero] using
    congrArg Neg.neg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mixedBoundary_eq_zero s I a b k hk)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (sum_rhsContribution_eq_zero)


/-- 概要：方程式の右辺の微分は、真部分集合の残差を含む寄与の和に等しい。
方針：微分した右辺の残差展開から純代数寄与の零の総和を除く。
規約：HA Proposition 1.3.1.10。使われ方：内部ホーンの未知の一面の残差を取り出す主恒等式。 -/
lemma bianchi {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    differential A (s.rhs I a b k hI ha hb hk) =
      ∑ j : I, if h : a < j.val ∧ j.val < b then
        s.residualContribution I a b k hI ha hb hk j.val j.property h.1 h.2 else 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_rhs_expansion, sum_rhsContribution_eq_zero, add_zero]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (bianchi)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
