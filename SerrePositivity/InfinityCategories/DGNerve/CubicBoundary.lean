module
public import SerrePositivity.InfinityCategories.DGNerve.NestedCut

/-! # 実際の三重合成の総和の相殺

概要：切断合成部分を左右でさらに合成した三重合成項の総和は零となる。
方針：左右の二重切断の合成値を結合律でそろえ、二重切断の係数の相殺を適用する。
規約：HA Proposition 1.3.1.10。使われ方：主残差恒等式の三重合成部分の消去。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：合成境界の左右の合成は、二つの切断順の三重合成の有限和に分かれる。
方針：合成を有限和へ分配し、左右の内部点集合を共通の添字へ移す。
規約：HA Proposition 1.3.1.10。使われ方：三重合成の総和を二重切断の和に戻す。 -/
lemma cutBoundary_quadratic {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (l : Fin (n + 1)) (hl : l ∈ I) (hal : a < l) (hlb : l < b) :
    s.cutBoundary s.quadraticBoundary I a b k l =
      (∑ j ∈ (Index.interior I a b).filter (l < ·), Index.sign (I.filter (l ≤ ·)) j •
        s.nestedCutRight I a b k l j) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        ∑ j ∈ (Index.interior I a b).filter (· < l), Index.sign (I.filter (· ≤ l)) j •
          s.nestedCutLeft I a b k j l := by
  have hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1 := by
    have := Index.split_card hl
    omega
  unfold cutBoundary
  rw [dite_eq_left hsum]
  simp only [quadraticBoundary, compose_sum_left, compose_sum_right,
    compose_units_smul_left, compose_units_smul_right,
    Index.interior_right_cut I a b l hal, Index.interior_left_cut I a b l hlb,
    nestedCutRight, nestedCutLeft, dite_eq_left hsum]

/-- 概要：実際の切断合成境界を元の成分と左右で合成した符号付き総和は零。
方針：二重切断の二つの合成値をそろえ、共通の値の二重和の係数を相殺する。
規約：HA Proposition 1.3.1.10。使われ方：残差恒等式に残る実際の三重合成項の消去。 -/
lemma cubicBoundary_eq_zero {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    ∑ l ∈ Index.interior I a b,
      Index.sign I l • s.cutBoundary s.quadraticBoundary I a b k l = 0 := by
  let K := Index.interior I a b
  have hcut :
      (∑ l ∈ K, Index.sign I l • s.cutBoundary s.quadraticBoundary I a b k l) =
      (∑ j ∈ K, Index.sign I j •
        ∑ l ∈ K.filter (j < ·), Index.sign (I.filter (j ≤ ·)) l •
          s.nestedCutLeft I a b k j l) +
      (∑ l ∈ K, Index.sign I l • ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        ∑ j ∈ K.filter (· < l), Index.sign (I.filter (· ≤ l)) j •
          s.nestedCutLeft I a b k j l)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hnest :
        (∑ l ∈ K.filter (j < ·), Index.sign (I.filter (j ≤ ·)) l •
          s.nestedCutRight I a b k j l) =
        ∑ l ∈ K.filter (j < ·), Index.sign (I.filter (j ≤ ·)) l •
          s.nestedCutLeft I a b k j l := by
      apply Finset.sum_congr rfl
      intro l hl
      have hl' := Finset.mem_filter.mp hl
      have hlI := (Finset.mem_filter.mp hl'.1).1
      rw [nestedCutRight_eq_left s I a b k hk j l hj'.1 hlI hl'.2]
    rw [cutBoundary_quadratic s I a b k hk j hj'.1 hj'.2.1 hj'.2.2, smul_add, hnest]
  change (∑ l ∈ K, Index.sign I l • s.cutBoundary s.quadraticBoundary I a b k l) = 0
  rw [hcut]
  exact Index.sum_double_cut_cancel I K (Finset.filter_subset _ _)
    (fun j l => s.nestedCutLeft I a b k j l)

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
