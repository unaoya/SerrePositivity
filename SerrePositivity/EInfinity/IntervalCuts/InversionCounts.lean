module

public import SerrePositivity.EInfinity.IntervalCuts.ActiveSigns
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# 活動位置の色の逆転数

概要：Berger–Fresse §2.2.4 の非零切断の交換指数を活動位置上の色の逆転数へ直す。
方針：区間長は活動位置で一、それ以外で零なので、二つの有限和を活動集合へ制限する。
規約：逆転は元位置 i<j かつ色 u(j)<u(i)。
使われ方：活動位置を一つ除いたときの切断符号の比較。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open scoped BigOperators

/-- 概要：元位置と色の順序が逆になる一対の寄与（BF §2.2.4）。
方針：厳密な二つの不等式で零または一を返す。
規約：同じ位置・同じ色の対は寄与しない。
使われ方：有限な活動集合の交換指数。 -/
def positionInversionTerm {n l : ℕ} (u : Fin l → Fin n) (i j : Fin l) : ℕ :=
  if i < j ∧ u j < u i then 1 else 0

/-- 概要：指定した位置集合での色の逆転数（BF §2.2.4）。
方針：全ての位置対の寄与を足す。
規約：同じ色を持つ位置があっても定義する。
使われ方：非零切断の符号と文字削除後の符号の比較。 -/
def positionInversionCount {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l)) : ℕ :=
  ∑ i ∈ s, ∑ j ∈ s, positionInversionTerm u i j

/-- 概要：非零切断の交換指数は活動位置の色の逆転数（BF §2.2.4）。
方針：活動位置以外の区間長が零であるため、両方の和を活動集合へ制限する。
規約：退化な切断については主張しない。
使われ方：一般の有限逆転数の削除公式を実際の切断へ適用する。 -/
lemma edgePermutationExponent_eq_inversionCount {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : EdgeNondegenerate u p) : edgePermutationExponent u p =
      positionInversionCount u (activePositions u p) := by
  unfold edgePermutationExponent positionInversionCount
  calc
    _ = ∑ i ∈ activePositions u p, ∑ j : Fin l,
        if i < j ∧ u j < u i then edgeIntervalLength u p i * edgeIntervalLength u p j
        else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp [edgeIntervalLength_of_nondegenerate h, hi]
    _ = ∑ i ∈ activePositions u p, ∑ j ∈ activePositions u p,
        if i < j ∧ u j < u i then edgeIntervalLength u p i * edgeIntervalLength u p j
        else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp [edgeIntervalLength_of_nondegenerate h, hj]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [edgeIntervalLength_of_nondegenerate h, ite_eq_left hi, ite_eq_left hj,
        one_mul, positionInversionTerm]

/-- 概要：非零切断の符号は活動位置の色の逆転数の −1 冪（BF §2.2.4）。
方針：位置指数零と交換指数の活動集合への制限を連結する。
規約：整数符号。
使われ方：削除符号とテンソル因子の境界符号の一致。 -/
lemma edgeSign_eq_inversionCount {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : EdgeNondegenerate u p) :
    edgeSign u p = (-1 : ℤ) ^ positionInversionCount u (activePositions u p) := by
  rw [edgeSign_of_nondegenerate h, edgePermutationExponent_eq_inversionCount h]

/-- 概要：位置を一つ除く逆転数の差は、その位置を含む二種類の対（BF §2.2.4）。
方針：外側と内側の有限和を指定位置と残りへ分ける。
規約：色の単射性は不要。
使われ方：削除前後の交換符号の指数を比較する。 -/
lemma positionInversionCount_erase {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l))
    (a : Fin l) (ha : a ∈ s) :
    positionInversionCount u s = positionInversionCount u (s.erase a) +
      (∑ j ∈ s, positionInversionTerm u a j) + (∑ j ∈ s, positionInversionTerm u j a) := by
  have hr (i : Fin l) : (∑ j ∈ s, positionInversionTerm u i j) =
      positionInversionTerm u i a + ∑ j ∈ s.erase a, positionInversionTerm u i j :=
    (Finset.add_sum_erase s _ ha).symm
  have hc : (∑ i ∈ s.erase a, positionInversionTerm u i a) =
      ∑ i ∈ s, positionInversionTerm u i a :=
    Finset.sum_erase s (by simp [positionInversionTerm])
  unfold positionInversionCount
  rw [← Finset.add_sum_erase s (fun i => ∑ j ∈ s, positionInversionTerm u i j) ha]
  have hrs : (∑ i ∈ s.erase a, ∑ j ∈ s, positionInversionTerm u i j) =
      ∑ i ∈ s.erase a, (positionInversionTerm u i a +
        ∑ j ∈ s.erase a, positionInversionTerm u i j) :=
    Finset.sum_congr rfl (fun i _ => hr i)
  rw [hrs, Finset.sum_add_distrib, hc]
  omega

end SerrePositivity.EInfinity.IntervalCuts
