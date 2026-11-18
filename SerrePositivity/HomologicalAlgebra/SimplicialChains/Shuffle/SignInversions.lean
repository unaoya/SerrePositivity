module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleEnumerationRank
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleStepMembership
public import Mathlib.GroupTheory.Perm.Fin

/-!
# shuffle の符号と逆転数

概要：Berger–Fresse §1.1.3–§1.1.4 の shuffle 符号を水平辺の前の垂直辺数で表す。
方針：逆置換の順序比較を辺の所属へ還元し、signature の積公式を用いる。
規約：各逆転は垂直辺が水平辺より先に現れる対として一度数える。
使われ方：切断した二経路の符号と Koszul 符号を比較する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：水平辺の前にある垂直辺の対の総数（Berger–Fresse §1.1.3）。
方針：各水平辺の厳密な接頭区間内の補集合の濃度を足す。
規約：空の辺集合・空の補集合では零。
使われ方：shuffle の signature と経路の連結の符号を計算する。 -/
def inversionNumber {N : ℕ} (S : Finset (Fin N)) : ℕ :=
  ∑ j ∈ S, (Sᶜ.filter (fun i => i.val < j.val)).card

/-- 概要：逆 shuffle 置換の逆転は垂直辺・水平辺の順の対に限る（BF §1.1.3）。
方針：辺の所属ごとの逆像座標公式と座標の単調性を使う。
規約：i は j より先の辺。
使われ方：signature の積公式を逆転数へ変換する。 -/
lemma inverse_lt_iff {p q : ℕ} (s : ShufflePath p q) (i j : Fin (p + q)) (hij : i < j) :
    s.permutation.symm i < s.permutation.symm j ↔ i ∈ s.val ∨ j ∉ s.val := by
  have hle : i.castSucc ≤ j.castSucc := by exact le_of_lt hij
  have hne : s.permutation.symm i ≠ s.permutation.symm j :=
    fun h => (ne_of_lt hij) (s.permutation.symm.injective h)
  by_cases hi : i ∈ s.val <;> by_cases hj : j ∈ s.val
  · have hm := s.horizontal.monotone hle
    have hl : s.permutation.symm i ≤ s.permutation.symm j := by
      simpa only [Fin.le_def, s.permutation_symm_val_of_mem i hi,
        s.permutation_symm_val_of_mem j hj] using hm
    simp only [hi, true_or, iff_true]
    exact lt_of_le_of_ne hl hne
  · have hb := (s.step_of_mem i hi).1
    have hbound := (s.horizontal i.succ).isLt
    rw [Fin.lt_def, s.permutation_symm_val_of_mem i hi,
      s.permutation_symm_val_of_notMem j hj]
    simp only [hi, true_or, iff_true]
    omega
  · have hb := (s.step_of_mem j hj).1
    have hbound := (s.horizontal j.succ).isLt
    rw [Fin.lt_def, s.permutation_symm_val_of_notMem i hi,
      s.permutation_symm_val_of_mem j hj]
    simp only [hi, hj, not_true_eq_false, or_self, iff_false]
    omega
  · have hm := s.vertical.monotone hle
    have hl : s.permutation.symm i ≤ s.permutation.symm j := by
      rw [Fin.le_def, s.permutation_symm_val_of_notMem i hi,
        s.permutation_symm_val_of_notMem j hj]
      exact Nat.add_le_add_left hm p
    simp only [hj, not_false_eq_true, or_true, iff_true]
    exact lt_of_le_of_ne hl hne

/-- 概要：shuffle の符号は逆転数による (−1) の冪である（BF §1.1.3）。
方針：逆置換の signature の積を水平辺の前の垂直辺についてまとめる。
規約：符号は整数の単元に値を取る。
使われ方：前後経路の符号の分解。 -/
lemma sign_eq_pow_inversionNumber {p q : ℕ} (s : ShufflePath p q) :
    s.sign = (-1 : ℤˣ) ^ _root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber s.val := by
  change Equiv.Perm.sign s.permutation = _
  rw [← Equiv.Perm.sign_symm, Equiv.Perm.sign_eq_prod_prod_Iio]
  have hinner (j : Fin (p + q)) :
      (∏ i ∈ Finset.Iio j,
        if s.permutation.symm i < s.permutation.symm j then (1 : ℤˣ) else -1) =
      if j ∈ s.val then (-1 : ℤˣ) ^ (s.valᶜ.filter (fun i => i.val < j.val)).card else 1 := by
    by_cases hj : j ∈ s.val
    · rw [ite_eq_left hj]
      have he : (Finset.Iio j).filter (fun i => i ∉ s.val) =
          s.valᶜ.filter (fun i => i.val < j.val) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_Iio, Finset.mem_compl, Fin.lt_def, and_comm]
      calc
        _ = ∏ i ∈ Finset.Iio j, if i ∉ s.val then (-1 : ℤˣ) else 1 := by
          apply Finset.prod_congr rfl
          intro i hi
          simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.inverse_lt_iff s i j (Finset.mem_Iio.mp hi)]
          by_cases hiS : i ∈ s.val <;> simp [hiS, hj]
        _ = ∏ _i ∈ (Finset.Iio j).filter (fun i => i ∉ s.val), (-1 : ℤˣ) := by
          rw [Finset.prod_filter]
        _ = _ := by rw [Finset.prod_const, he]
    · rw [ite_eq_right hj]
      apply Finset.prod_eq_one
      intro i hi
      simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.inverse_lt_iff s i j (Finset.mem_Iio.mp hi)]
      simp [hj]
  simp_rw [hinner]
  rw [← Finset.prod_filter]
  have hfilter : Finset.univ.filter (fun j => j ∈ s.val) = s.val := by ext j; simp
  rw [hfilter, Finset.prod_pow_eq_pow_sum]
  rfl

end SerrePositivity.SimplicialChains.Shuffle
