module

public import SerrePositivity.EInfinity.SimplexCuts.AdjacentColorDeletions

/-!
# 混合角の位置符号と削除係数

Berger–Fresse §2.2.7、M14 L09a。
同じ削除色列の隣接順位と、既存の位置指数の増分を組み合わせる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C144：混合角での位置符号と単語削除係数は反対。 -/
lemma signedDeletionCoefficient_swapSteps_hv {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val) :
    (-1 : ℤ) ^ positionExponent (s.swapSteps a b) v *
        Surjection.deletionCoefficient (label (s.swapSteps a b) v) b.castSucc =
      -((-1 : ℤ) ^ positionExponent s v *
        Surjection.deletionCoefficient (label s v) b.castSucc) := by
  let t := s.swapSteps a b
  have hna : a ∉ t.val := by
    simpa only [t, BarrattEccles.ShufflePath.mem_swapSteps, Equiv.swap_apply_left] using hb
  have hbc : b.castSucc = a.succ := Fin.ext hab
  have hsame : label t v a.castSucc = label t v b.castSucc := by
    rw [hbc]
    exact congrArg v (t.step_of_notMem a hna).1.symm
  have hOld : Surjection.Caesura (label s v) b.castSucc :=
    (Finset.mem_filter.mp (before_vertical_active s v b hb)).2
  have hNew : Surjection.Caesura (label t v) a.castSucc :=
    (Finset.mem_filter.mp (before_vertical_active t v a hna)).2
  have he : Surjection.erase (label t v) a.castSucc =
      Surjection.erase (label s v) b.castSucc :=
    (erase_adjacent_equal (label t v) a.castSucc b.castSucc hab hsame).trans
      (erase_label_swapSteps s v a b hab)
  have hc : Surjection.Caesura (Surjection.erase (label s v) b.castSucc) a ↔
      Surjection.Caesura v (s.horizontal a.castSucc) := by
    have hlt : a.castSucc < b.castSucc := by change a.val < b.val; omega
    rw [IntervalCuts.caesura_erase_of_caesura _ _ hOld,
      Fin.succAbove_of_castSucc_lt b.castSucc a hlt]
    simpa only [activeVertexPositions, Finset.mem_filter, Finset.mem_univ, true_and] using
      before_horizontal_active_iff s v a ha
  have ho := deletionCoefficient_erase_active_rank (label s v) b.castSucc hOld b rfl
  have hn := deletionCoefficient_erase_active_rank (label t v) a.castSucc hNew a rfl
  rw [he] at hn
  have hd := deletionCoefficient_adjacent_equal (label t v) a.castSucc b.castSucc hab hsame
  rw [hn] at hd
  rw [hd, ho, caesuraRank_adjacent _ a b hab,
    positionExponent_swapSteps_hv s v a b hab ha hb]
  by_cases h : Surjection.Caesura v (s.horizontal a.castSucc)
  · have hh := hc.mpr h
    simp only [h, hh, ite_true, pow_succ, mul_neg, neg_mul, neg_neg, mul_one]
  · have hh : ¬Surjection.Caesura (Surjection.erase (label s v) b.castSucc) a :=
      fun h' => h (hc.mp h')
    simp only [h, hh, ite_false, Nat.add_zero, mul_neg]

end SerrePositivity.EInfinity.SimplexCuts
