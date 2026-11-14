module

public import SerrePositivity.EInfinity.IntervalCuts.InversionCounts

/-!
# 色順の並べ替えと一文字の境界符号

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
既存の有限逆転数の削除公式を使い、色順の境界番号を元位置順の境界番号へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open SerrePositivity.EInfinity.IntervalCuts
  (positionInversionTerm positionInversionCount positionInversionCount_erase)

/-- C98の証明分割：一つの他の位置が削除符号へ与える寄与。 -/
lemma colorSorting_boundary_term {N r : ℕ} (v : Fin N → Fin r) (a b : Fin N) :
    positionInversionTerm v a b + positionInversionTerm v b a +
      (if v b < v a then 1 else 0) + (if b < a ∧ v b = v a then 1 else 0) =
    (if b < a then 1 else 0) + 2 * positionInversionTerm v a b := by
  by_cases hab : a = b
  · subst b
    simp [positionInversionTerm]
  · have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
    unfold positionInversionTerm
    simp only [Fin.lt_def, Fin.ext_iff]
    split_ifs <;> omega

/-- C98：色順の境界指数と元位置順の境界指数との差は偶数。 -/
lemma positionInversionCount_boundary {N r : ℕ} (v : Fin N → Fin r)
    (s : Finset (Fin N)) (a : Fin N) (ha : a ∈ s) :
    positionInversionCount v s + (s.filter (fun b => v b < v a)).card +
      (s.filter (fun b => b < a ∧ v b = v a)).card =
    positionInversionCount v (s.erase a) + (s.filter (fun b => b < a)).card +
      2 * (∑ b ∈ s, positionInversionTerm v a b) := by
  have ht : (∑ b ∈ s, positionInversionTerm v a b) +
      (∑ b ∈ s, positionInversionTerm v b a) +
      (s.filter (fun b => v b < v a)).card +
      (s.filter (fun b => b < a ∧ v b = v a)).card =
      (s.filter (fun b => b < a)).card + 2 * (∑ b ∈ s, positionInversionTerm v a b) := by
    have h := Finset.sum_congr rfl (fun b (_ : b ∈ s) => colorSorting_boundary_term v a b)
    simpa only [Finset.sum_add_distrib, Finset.card_filter, Finset.mul_sum] using h
  have he := positionInversionCount_erase v s a ha
  omega

/-- C99：色順のKoszul境界符号は、残った逆転符号と元位置順の面符号の積。 -/
lemma colorSorting_boundary_sign {N r : ℕ} (v : Fin N → Fin r)
    (s : Finset (Fin N)) (a : Fin N) (ha : a ∈ s) :
    (-1 : ℤ) ^ (positionInversionCount v s + (s.filter (fun b => v b < v a)).card +
      (s.filter (fun b => b < a ∧ v b = v a)).card) =
    (-1 : ℤ) ^ positionInversionCount v (s.erase a) *
      (-1 : ℤ) ^ (s.filter (fun b => b < a)).card := by
  rw [positionInversionCount_boundary v s a ha, pow_add, pow_add, pow_mul]
  simp

end SerrePositivity.EInfinity.SimplexCuts
