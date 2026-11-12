module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Tactic.Ring

/-!
# May の P⁰ の整数次数の正規化

May, Definition 2.2 の ν(n) と D_{−n(p−1)} の添字。
ν(n) = (−1)^{n(n−1)m/2}(m!)^n、m=(p−1)/2 とし、負の n では単元の逆冪を使う。
ホモロジー次数 n は本体の余鎖次数 −n に対応する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
variable (p : ℕ) [Fact p.Prime]

lemma mayHalfFactorial_ne_zero : (((p - 1) / 2).factorial : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff, (Fact.out : Nat.Prime p).dvd_factorial]
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have h : (p - 1) / 2 < p := lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt hp (by omega))
  omega

/-- May の階乗の係数は F_p の単元。 -/
def mayHalfFactorialUnit : (ZMod p)ˣ :=
  Units.mk0 (((p - 1) / 2).factorial : ZMod p) (mayHalfFactorial_ne_zero p)

/-- 全整数のホモロジー次数に対する May の指定正規化。 -/
def mayNu (n : ℤ) : (ZMod p)ˣ :=
  (-1 : (ZMod p)ˣ) ^ (n * (n - 1) * ((p - 1) / 2 : ℕ) / 2) *
    mayHalfFactorialUnit p ^ n

lemma mayNu_zero : mayNu p 0 = 1 := by simp [mayNu]

lemma mayNu_ne_zero (n : ℤ) : (mayNu p n : ZMod p) ≠ 0 := Units.ne_zero _

lemma mayNu_two (n : ℤ) : mayNu 2 n = 1 := by
  simp [mayNu, mayHalfFactorialUnit]

/-- ホモロジー次数を保つ P⁰ の係数の鎖次数。 -/
def mayZeroIndex (n : ℤ) : ℤ := -n * (p - 1 : ℕ)

omit [Fact p.Prime] in
lemma mayZeroIndex_zero : mayZeroIndex p 0 = 0 := by simp [mayZeroIndex]

lemma mayZeroIndex_negative {n : ℤ} (hn : 0 < n) : mayZeroIndex p n < 0 := by
  have hp : 0 < (p - 1 : ℕ) := Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hn) (by exact_mod_cast hp)

lemma mayZeroIndex_degree (n : ℤ) : p * n + mayZeroIndex p n = n := by
  have hp : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
  simp only [mayZeroIndex, Nat.cast_sub hp, Nat.cast_one]
  ring

end SerrePositivity.EInfinity.PowerOperation
