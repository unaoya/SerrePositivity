module

public import SerrePositivity.EInfinity.Surjection.OccurrenceBoundaries
public import SerrePositivity.EInfinity.Surjection.LineRanks
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# 外側成分の総次数と後続成分の次数

概要：Berger–Fresse §1.2.5 の外側語の成分次数と右からの代入で通過する次数を計算する。
方針：出現境界の単調な行番号の差を全範囲・後続範囲で望遠鏡和として足す。
規約：指定値の出現の前後に一成分ずつ置く。
使われ方：BF §1.5 の経路の水平辺数と Koszul 交換の符号を照合する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection

/-- 概要：出現で切った外側の一成分の行次数（BF §1.2.5）。
方針：成分の両端で行番号の差を取る。
規約：最後以降は次数零。
使われ方：外側の成分ごとの水平辺数。 -/
def outerSegmentDegree {n l : ℕ} (v : Fin l → Fin n) (k : Fin n) (i : ℕ) : ℕ :=
  lineRank v (occurrenceBoundary v k (i + 1)) - lineRank v (occurrenceBoundary v k i)

/-- 概要：全外側成分の次数の和は元の次数（BF §1.2.5）。
方針：単調な境界列の行番号の差を望遠鏡和にする。
規約：成分数は指定値の出現回数＋1。
使われ方：合成経路の水平辺数 d を供給する。 -/
lemma sum_outerSegmentDegree {n d : ℕ} (v : BasisWord n d) (k : Fin n) :
    (∑ i : Fin (occurrenceCount v.val k + 1), outerSegmentDegree v.val k i.val) = d := by
  unfold outerSegmentDegree
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    lineRank v.val (occurrenceBoundary v.val k (i + 1)) -
      lineRank v.val (occurrenceBoundary v.val k i)) (occurrenceCount v.val k + 1)]
  have hm : Monotone (fun i => lineRank v.val (occurrenceBoundary v.val k i)) :=
    (lineRank_mono v.val).comp (occurrenceBoundary_mono v.val k)
  rw [Finset.sum_range_tsub hm, occurrenceBoundary_last, occurrenceBoundary_zero,
    lineRank_zero, Nat.sub_zero, lineRank_last]

/-- 概要：単調な自然数列の行番号の差の区間和（BF §1.2.5）。
方針：零からの二つの望遠鏡和の差を取る。
規約：a≤b。
使われ方：指定出現より後にある外側成分の総次数を求める。 -/
lemma sum_Ico_monotone_differences (f : ℕ → ℕ) (hf : Monotone f) (a b : ℕ) (hab : a ≤ b) :
    (∑ i ∈ Finset.Ico a b, (f (i + 1) - f i)) = f b - f a := by
  have hs := Finset.sum_range_add_sum_Ico (fun i => f (i + 1) - f i) hab
  rw [Finset.sum_range_tsub hf, Finset.sum_range_tsub hf] at hs
  have ha := hf (Nat.zero_le a)
  have hb := hf hab
  omega

/-- 概要：指定出現以降の外側成分の総次数は元の次数−その行番号（BF §1.2.5）。
方針：後続範囲の望遠鏡和の始点を指定出現、終点を元の最後の行に同定する。
規約：指定出現を含む行から後続を数える。
使われ方：合成符号の指数を実際の成分交換の次数積へ戻す。 -/
lemma sum_outerSegmentDegree_suffix {n d : ℕ} (v : BasisWord n d) (k : Fin n)
    (j : Fin (occurrenceCount v.val k)) :
    (∑ i ∈ Finset.Ico (j.val + 1) (occurrenceCount v.val k + 1),
      outerSegmentDegree v.val k i) = d - caesuraRank v.val (occurrenceAt v.val k j) := by
  unfold outerSegmentDegree
  have hm : Monotone (fun i => lineRank v.val (occurrenceBoundary v.val k i)) :=
    (lineRank_mono v.val).comp (occurrenceBoundary_mono v.val k)
  rw [sum_Ico_monotone_differences _ hm _ _ (by have := j.isLt; omega)]
  rw [occurrenceBoundary_last, occurrenceBoundary_at, lineRank_last, lineRank_fin]

/-- 概要：合成符号の指数は交換する内側成分と全後続外側成分の次数積（BF §1.2.5）。
方針：後続外側成分の総次数を定義済みの順位差へ照合する。
規約：右から順に内側成分を挿入する。
使われ方：BF §1.5 の shuffle 符号との一致を証明する基礎。 -/
lemma compositionExponent_eq_component_exchanges {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) :
    compositionExponent u v k r = ∑ j : Fin (occurrenceCount u.val k),
      segmentDegree v.val r j *
        ∑ i ∈ Finset.Ico (j.val + 1) (occurrenceCount u.val k + 1),
          outerSegmentDegree u.val k i := by
  simp_rw [sum_outerSegmentDegree_suffix]
  rfl

end SerrePositivity.EInfinity.Surjection
