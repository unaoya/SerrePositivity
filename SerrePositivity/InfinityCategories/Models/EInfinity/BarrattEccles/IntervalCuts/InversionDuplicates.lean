module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InversionDeletion

/-!
模型。文献の定義との比較は後で
# 同色位置を含む活動集合の削除符号

概要：Berger–Fresse §2.2.7 の退化元切断に必要な、色が単射でない逆転数の削除公式。
方針：同色の先行位置の個数を補正項に加え、隣り合う同色出現の二削除を比較する。
規約：同色出現の間には別の同色を置かないが、他色は何個あってもよい。
使われ方：元の同色が三回現れる余分な削除項の係数反対性。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open scoped _root_.BigOperators

/-- 概要：指定位置より前の同色位置の個数（BF §2.2.7）。
方針：有限位置集合を位置と色の一致で切る。
規約：指定位置自身は含まない。
使われ方：非単射な色族の逆転数公式の補正項。 -/
def equalBeforeRank {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l)) (a : Fin l) : ℕ :=
  (s.filter (fun j => j < a ∧ u j = u a)).card

private lemma inversion_rank_pointwise_general {n l : ℕ} (u : Fin l → Fin n) (a j : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u a j + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u j a +
        2 * (if j < a ∧ u j < u a then 1 else 0) + (if j < a ∧ u j = u a then 1 else 0) =
      (if j < a then 1 else 0) + (if u j < u a then 1 else 0) := by
  rcases lt_trichotomy j a with hp | rfl | hp
  · rcases lt_trichotomy (u j) (u a) with hc | hc | hc
    · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, hp, not_lt_of_ge hp.le, hc, not_lt_of_ge hc.le, ne_of_lt hc]
    · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, hp, not_lt_of_ge hp.le, hc]
    · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, hp, not_lt_of_ge hp.le, hc, not_lt_of_ge hc.le, ne_of_gt hc]
  · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm]
  · rcases lt_trichotomy (u j) (u a) with hc | hc | hc
    · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, hp, not_lt_of_ge hp.le, hc, not_lt_of_ge hc.le, ne_of_lt hc]
    · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, hp, not_lt_of_ge hp.le, hc]
    · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, hp, not_lt_of_ge hp.le, hc, not_lt_of_ge hc.le, ne_of_gt hc]

/-- 概要：同色を許す逆転数の削除公式（BF §2.2.7）。
方針：各位置との比較を足し、同色先行数を補正する。
規約：色の単射性は不要。
使われ方：退化元切断の活動集合へ削除符号の計算を適用する。 -/
lemma positionInversionCount_erase_balance_general {n l : ℕ} (u : Fin l → Fin n)
    (s : Finset (Fin l)) (a : Fin l) (ha : a ∈ s) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u s + 2 * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.lowerRank u s a + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.equalBeforeRank u s a =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (s.erase a) + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank s a + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorRank u s a := by
  have hs := Finset.sum_congr rfl (fun j (_ : j ∈ s) => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.inversion_rank_pointwise_general u a j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole] at hs
  change (∑ j ∈ s, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u a j) +
      (∑ j ∈ s, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u j a) + 2 * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.lowerRank u s a + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.equalBeforeRank u s a =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank s a + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorRank u s a at hs
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_erase u s a ha]
  omega

/-- 概要：連続する同色出現の先行同色数は一つ増える（BF §2.2.7）。
方針：後の位置の先行同色集合は、前の集合に前の位置を加えたもの。
規約：二位置の間に同色の活動位置がないことだけを要求する。
使われ方：二削除の交換符号が反対になることを示す。 -/
lemma equalBeforeRank_succ {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l))
    (a b : Fin l) (ha : a ∈ s) (hab : a < b) (hu : u a = u b)
    (hgap : ∀ j ∈ s, a < j → j < b → u j ≠ u b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.equalBeforeRank u s b = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.equalBeforeRank u s a + 1 := by
  have hs : s.filter (fun j => j < b ∧ u j = u b) =
      insert a (s.filter (fun j => j < a ∧ u j = u a)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hj, hjb, huj⟩
      by_cases hja : j = a
      · exact Or.inl hja
      · right
        have hja' : j < a := by
          rcases lt_or_gt_of_ne hja with hja' | haj
          · exact hja'
          · exact False.elim (hgap j hj haj hjb huj)
        exact ⟨hj, hja', huj.trans hu.symm⟩
    · rintro (rfl | ⟨hj, hja, huj⟩)
      · exact ⟨ha, hab, hu⟩
      · exact ⟨hj, lt_trans hja hab, huj.trans hu⟩
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.equalBeforeRank
  rw [hs, Finset.card_insert_of_notMem (by simp)]

/-- 概要：連続する同色活動位置の二削除は位置符号付き交換符号が反対（BF §2.2.7）。
方針：一般の逆転数公式を二位置で比較し、先行同色数の差一を使う。
規約：他の色の重複を排除する仮定も不要。
使われ方：同色三出現の退化元切断から来る二項の相殺。 -/
lemma positionInversionSign_erase_same_color {n l : ℕ} (u : Fin l → Fin n)
    (s : Finset (Fin l)) (a b : Fin l) (ha : a ∈ s) (hb : b ∈ s)
    (hab : a < b) (hu : u a = u b) (hgap : ∀ j ∈ s, a < j → j < b → u j ≠ u b) :
    (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank s a * (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (s.erase a) =
      -((-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank s b * (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (s.erase b)) := by
  have hA := congrArg (fun r : ℕ => (r : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_erase_balance_general u s a ha)
  have hB := congrArg (fun r : ℕ => (r : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_erase_balance_general u s b hb)
  have hE := congrArg (fun r : ℕ => (r : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.equalBeforeRank_succ u s a b ha hab hu hgap)
  have hC : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorRank u s a = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorRank u s b := by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorRank, hu]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hA hB hE
  have hU : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank s a + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (s.erase a) : ℕ) : ℤ).negOnePow =
      (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank s b + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (s.erase b) : ℕ) : ℤ) + 1).negOnePow := by
    apply (Int.negOnePow_eq_iff _ _).2
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.lowerRank u s a : ℤ) - (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.lowerRank u s b : ℤ) - 1, ?_⟩
    simp only [Nat.cast_add]
    rw [hC] at hA
    omega
  rw [Int.negOnePow_succ] at hU
  simpa only [Int.coe_negOnePow_natCast, Units.val_neg, pow_add]
    using congrArg (fun z : ℤˣ => (z : ℤ)) hU

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
