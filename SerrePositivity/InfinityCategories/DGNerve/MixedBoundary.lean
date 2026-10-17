module
public import SerrePositivity.InfinityCategories.DGNerve.CutBoundary

/-! # 実際の削除・切断の混合和の相殺

概要：削除後の合成境界と、切断後の線形境界の合成の和が零であることを示す。
方針：実際の合成値を削除後の切断合成へそろえ、混合二重和の符号相殺を適用する。
規約：HA Proposition 1.3.1.10。使われ方：主残差恒等式の混合部分の消去。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：削除後の合成境界と切断後の線形境界の合成の符号付き総和は零。
方針：切断境界の線形部分を左右の共通の切断合成へ展開し、混合二重和を相殺する。
規約：HA Proposition 1.3.1.10。使われ方：実際の斉次成分に対する混合項の一括消去。 -/
lemma mixedBoundary_eq_zero {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    (∑ j ∈ Index.interior I a b, Index.sign I j • s.quadraticBoundary (I.erase j) a b (k + 1)) +
      (∑ l ∈ Index.interior I a b,
        Index.sign I l • s.cutBoundary s.linearBoundary I a b k l) = 0 := by
  let K := Index.interior I a b
  have hcut :
      (∑ l ∈ K, Index.sign I l • s.cutBoundary s.linearBoundary I a b k l) =
      (∑ l ∈ K, Index.sign I l •
        ∑ j ∈ K.filter (l < ·), Index.sign (I.filter (l ≤ ·)) j •
          s.cutCompose (I.erase j) a b (k + 1) l) +
      (∑ l ∈ K, Index.sign I l • ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        ∑ j ∈ K.filter (· < l), Index.sign (I.filter (· ≤ l)) j •
          s.cutCompose (I.erase j) a b (k + 1) l)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    have hl' := Finset.mem_filter.mp hl
    rw [cutBoundary_linear s I a b k hk l hl'.1 hl'.2.1 hl'.2.2, smul_add]
  change (∑ j ∈ K, Index.sign I j • s.quadraticBoundary (I.erase j) a b (k + 1)) +
    (∑ l ∈ K, Index.sign I l • s.cutBoundary s.linearBoundary I a b k l) = 0
  rw [hcut]
  simp only [quadraticBoundary, Index.interior_erase]
  have hh := Index.sum_mixed_cancel I K (Finset.filter_subset _ _)
    (fun j l => s.cutCompose (I.erase j) a b (k + 1) l)
  simpa only [add_assoc] using hh

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
