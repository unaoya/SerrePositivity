module
public import SerrePositivity.InfinityCategories.DGNerve.CubicBoundary

/-! # dg nerve の主残差恒等式

概要：方程式の右辺を微分すると、真部分集合の残差だけを含む和になる。
方針：純代数寄与を二重削除・混合・三重合成に分け、証明済みの三つの相殺を適用する。
規約：HA Proposition 1.3.1.10。使われ方：内部ホーンの欠けた面の方程式の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：純代数寄与は二重削除・混合・三重合成の各項に分かれる。
方針：真部分集合の右辺を線形部分と合成部分に分け、合成を差へ分配する。
規約：HA Proposition 1.3.1.10。使われ方：三つの相殺を元の寄与に接続する。 -/
lemma rhsContribution_eq_boundaries {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    s.rhsContribution I a b k hI ha hb hk j hj haj hjb = Index.sign I j •
      (s.linearBoundary (I.erase j) a b (k + 1) - s.quadraticBoundary (I.erase j) a b (k + 1) -
        s.cutBoundary s.linearBoundary I a b k j +
        s.cutBoundary s.quadraticBoundary I a b k j) := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by rw [hb]; exact I.isGreatest_max' _
  have hL := Index.left_two hamin.1 hj haj
  have hR := Index.right_two hj hbmax.1 hjb
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := Index.split_card hj
    omega
  simp only [rhsContribution, rhs_eq_linear_sub_quadratic, cutBoundary, dite_eq_left hsum]
  rw [homOrZero_eq s _ _ _ _ hL (Index.left_min hamin haj.le _) (Index.left_max hj _) rfl,
    homOrZero_eq s _ _ _ _ hR (Index.right_min hj _) (Index.right_max hbmax hjb.le _) rfl]
  simp only [compose_sub_left, compose_sub_right, smul_sub, smul_add]
  abel

/-- 概要：単体データの純代数寄与の総和は零。
方針：共通の内部点集合上で二重削除・混合・三重合成の三つの相殺を適用する。
規約：HA Proposition 1.3.1.10。使われ方：残差展開から主残差恒等式を得る。 -/
lemma sum_rhsContribution_eq_zero {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (∑ j : I, if h : a < j.val ∧ j.val < b then
      s.rhsContribution I a b k hI ha hb hk j.val j.property h.1 h.2 else 0) = 0 := by
  have heq :
      (∑ j : I, if h : a < j.val ∧ j.val < b then
        s.rhsContribution I a b k hI ha hb hk j.val j.property h.1 h.2 else 0) =
      ∑ j ∈ Index.interior I a b, Index.sign I j •
        (s.linearBoundary (I.erase j) a b (k + 1) - s.quadraticBoundary (I.erase j) a b (k + 1) -
          s.cutBoundary s.linearBoundary I a b k j +
          s.cutBoundary s.quadraticBoundary I a b k j) := by
    rw [Index.interior, Finset.sum_filter, ← Finset.sum_coe_sort I]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hint : a < j.val ∧ j.val < b
    · simp only [dite_eq_left hint, ite_eq_left hint]
      exact rhsContribution_eq_boundaries s I a b k hI ha hb hk j.val j.property hint.1 hint.2
    · simp only [dite_eq_right hint, ite_eq_right hint]
  rw [heq]
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [linearBoundary_squared, cubicBoundary_eq_zero s I a b k hk]
  simpa only [zero_sub, sub_eq_add_neg, add_zero, zero_add, neg_add, neg_zero] using
    congrArg Neg.neg (mixedBoundary_eq_zero s I a b k hk)

/-- 概要：方程式の右辺の微分は、真部分集合の残差を含む寄与の和に等しい。
方針：微分した右辺の残差展開から純代数寄与の零の総和を除く。
規約：HA Proposition 1.3.1.10。使われ方：内部ホーンの未知の一面の残差を取り出す主恒等式。 -/
lemma bianchi {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    differential A (s.rhs I a b k hI ha hb hk) =
      ∑ j : I, if h : a < j.val ∧ j.val < b then
        s.residualContribution I a b k hI ha hb hk j.val j.property h.1 h.2 else 0 := by
  rw [differential_rhs_expansion, sum_rhsContribution_eq_zero, add_zero]

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
