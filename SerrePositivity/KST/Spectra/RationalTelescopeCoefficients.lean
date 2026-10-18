module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.Factorial.Basic

/-!
概要：有理化の乗法列 2,3,4,… の区間係数と分母の共終性。
方針：区間積を遷移係数とし、十分後の一つの因子を指定した整数の倍数に取る。
規約：段 i から i+1 の係数は i+2。全ての非零整数を反転する。
使われ方：BF 1978 §2、HA §1.4.2。telescope の群と ℚ テンソルの比較の算術。
-/

@[expose] public section

namespace SerrePositivity.KST.Spectra.RationalTelescope

/-- 概要：乗法列の二段間の自然数係数。
方針：2,3,… の対応する有限区間積を取る。
規約：i=j では空積の一。
使われ方：BF 1978 §2、HA §1.4.2。有理化の群の遷移係数。 -/
def coefficient (i j : ℕ) : ℕ := ∏ k ∈ Finset.Ico i j, (k + 2)

/-- 概要：同じ段の遷移係数は一。
方針：同じ端点の区間は空。
規約：全ての自然数 i。
使われ方：HA §1.4.2。有理化の乗法図式の恒等条件。 -/
@[simp]
theorem coefficient_self (i : ℕ) : coefficient i i = 1 := by simp [coefficient]

/-- 概要：二つの連続する遷移係数の積は合成の係数。
方針：隣接区間の積の分解を使う。
規約：右の遷移の係数を左から掛ける。
使われ方：HA §1.4.2。有理化の乗法図式の合成条件。 -/
theorem coefficient_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    coefficient i k = coefficient j k * coefficient i j := by
  unfold coefficient
  rw [← Finset.prod_Ico_consecutive (fun r : ℕ ↦ r + 2) hij hjk, Nat.mul_comm]

/-- 概要：一段先への遷移係数は i+2。
方針：一つの元からなる区間積を計算する。
規約：最初の係数は二。
使われ方：HA §1.4.2。telescope の逐次乗法写像。 -/
@[simp]
theorem coefficient_step (i : ℕ) : coefficient i (i + 1) = i + 2 := by simp [coefficient]

/-- 概要：全ての区間係数は正。
方針：各因子 k+2 の正値性から積の正値性を得る。
規約：空区間も含む。
使われ方：HA §1.4.2。局所化の分母が非零であること。 -/
theorem coefficient_pos (i j : ℕ) : 0 < coefficient i j := by
  unfold coefficient
  apply Finset.prod_pos
  intro k _
  omega

/-- 概要：零段からの係数は階乗。
方針：後続段の合成式と階乗の漸化式を比較する。
規約：零段では一であり、j 段の分母は (j+1)!。
使われ方：HA §1.4.2。有理化の分数表示の分母。 -/
theorem coefficient_zero (j : ℕ) : coefficient 0 j = (j + 1).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [coefficient_comp (Nat.zero_le j) (Nat.le_succ j), coefficient_step, ih]
      exact (Nat.factorial_succ (j + 1)).symm

/-- 概要：任意の正整数は、任意の段から十分先への遷移係数を割る。
方針：区間内の一つの因子を (i+2)m に取る。
規約：どの始段 i に対しても分母が共終であることを示す。
使われ方：HA §1.4.2。乗法列の余極限で全正整数を反転する。 -/
theorem exists_dvd_coefficient (i m : ℕ) (hm : 0 < m) :
    ∃ j, i ≤ j ∧ m ∣ coefficient i j := by
  let N := (i + 2) * m
  have hN : i + 2 ≤ N := Nat.le_mul_of_pos_right (i + 2) hm
  have hr : N - 2 ∈ Finset.Ico i (N - 1) := by
    simp only [Finset.mem_Ico]
    omega
  have hd : m ∣ (N - 2) + 2 := by
    have h : (N - 2) + 2 = N := by omega
    rw [h]
    exact ⟨i + 2, Nat.mul_comm _ _⟩
  refine ⟨N - 1, by omega, ?_⟩
  exact hd.trans (Finset.dvd_prod_of_mem (fun r : ℕ ↦ r + 2) hr)

/-- 概要：区間係数を整数として扱う。
方針：自然数の積の標準埋め込みを使う。
規約：ℤ 加群のスカラーとして用いる。
使われ方：HA §1.4.2。アーベル群の有理化の線形遷移射。 -/
def integerCoefficient (i j : ℕ) : ℤ := coefficient i j

/-- 概要：整数係数の同じ段の遷移は一。
方針：自然数係数の恒等式を整数へ移す。
規約：ℤ 加群の恒等写像の係数。
使われ方：HA §1.4.2。乗法列の directed system 条件。 -/
@[simp]
theorem integerCoefficient_self (i : ℕ) : integerCoefficient i i = 1 := by
  simp [integerCoefficient]

/-- 概要：整数係数も連続する二遷移の積として合成する。
方針：自然数係数の合成式を整数へ移す。
規約：右の遷移の係数を左から掛ける。
使われ方：HA §1.4.2。乗法列の線形遷移の合成。 -/
theorem integerCoefficient_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    integerCoefficient i k = integerCoefficient j k * integerCoefficient i j := by
  simp only [integerCoefficient, coefficient_comp hij hjk, Nat.cast_mul]

/-- 概要：整数の区間係数は非零。
方針：自然数係数の正値性を使う。
規約：全ての段対で有効。
使われ方：HA §1.4.2。非零整数による加群の局所化。 -/
theorem integerCoefficient_ne_zero (i j : ℕ) : integerCoefficient i j ≠ 0 := by
  simp only [integerCoefficient, ne_eq, Int.natCast_eq_zero]
  exact Nat.ne_of_gt (coefficient_pos i j)

/-- 概要：任意の非零整数は十分先への整数遷移係数を割る。
方針：絶対値の自然数で分母の共終性を使う。
規約：負の整数も含む。
使われ方：HA §1.4.2。全ての非零整数の反転。 -/
theorem exists_dvd_integerCoefficient (i : ℕ) (m : ℤ) (hm : m ≠ 0) :
    ∃ j, i ≤ j ∧ m ∣ integerCoefficient i j := by
  obtain ⟨j, hij, hj⟩ := exists_dvd_coefficient i m.natAbs (Int.natAbs_pos.mpr hm)
  exact ⟨j, hij, Int.dvd_natCast.mpr hj⟩

end SerrePositivity.KST.Spectra.RationalTelescope
