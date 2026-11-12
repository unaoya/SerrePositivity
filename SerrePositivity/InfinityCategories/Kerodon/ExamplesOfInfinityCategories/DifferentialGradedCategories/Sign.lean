module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Tactic

/-!
# N4 座標と標準 Dold–Kan 座標の符号

概要：次数 k の符号 ε_k=(−1)^(k choose 2) と微分・積に必要な恒等式を証明する。
方針：二項係数の漸化式と符号の平方が1であることを使う。
規約：係数は整数とし、任意の加法可換群に作用させる。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ）・2.5.9（Tag 00SC） の線形 Hom と AW 積の座標変換。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：N4 の次数 k の座標を標準 chain map 座標へ移す整数符号。
方針：k 個の要素の反転数の偶奇を取る。
規約：k=0,1 では1、k=2,3 では−1。
使われ方：HA 1.3.1.12 の符号変更と Kerodon 2.5.9（Tag 00SC） の立方体の向き。 -/
def degreeSign (k : ℕ) : ℤ := (-1) ^ k.choose 2

/-- 概要：次の次数の符号は前の符号に (−1)^k を掛けたもの。
方針：二項係数の漸化式を使う。
規約：整数の通常の自然数べき。
使われ方：HA 1.3.1.12 の微分方程式の変換。 -/
lemma degreeSign_succ (k : ℕ) : degreeSign (k + 1) = (-1 : ℤ) ^ k * degreeSign k := by
  simp only [degreeSign, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]

/-- 概要：次数の符号の平方は1である。
方針：べきの積を底の積のべきに戻す。
規約：全ての非負次数。
使われ方：HA 1.3.1.12 の座標変換の逆写像。 -/
lemma degreeSign_mul_self (k : ℕ) : degreeSign k * degreeSign k = 1 := by
  simp only [degreeSign, ← mul_pow, neg_one_mul, neg_neg, one_pow]

/-- 概要：次数の和の符号は二つの符号と交差項 (−1)^(p q) の積である。
方針：二項係数の和の公式を次数に関して帰納し、べきを分解する。
規約：整数の積の順序は任意に交換できる。
使われ方：HA 1.3.1.13、Kerodon 2.5.9.2（Tag 00SE） の AW 合成の N4 座標への変換。 -/
lemma degreeSign_add (p q : ℕ) :
    degreeSign (p + q) = (-1 : ℤ) ^ (p * q) * degreeSign p * degreeSign q := by
  have hc : (p + q).choose 2 = p.choose 2 + q.choose 2 + p * q := by
    induction p with
    | zero => simp
    | succ p hp =>
      rw [Nat.succ_add, Nat.choose_succ_succ, Nat.choose_one_right, hp,
        Nat.choose_succ_succ, Nat.choose_one_right]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
      ring
  simp only [degreeSign, hc, pow_add]
  ring

/-- 概要：N4 の微分の次数符号は座標変換によって一つ前の次数の符号になる。
方針：次数の漸化式と偶数べきが1であることを使う。
規約：元の成分の次数は k+1 とし、零次数の微分は別に閉元として扱う。
使われ方：HA 1.3.1.12 の標準単体 chain map 方程式への変換。 -/
lemma degreeSign_differential (k : ℕ) :
    degreeSign (k + 1) * (-1 : ℤ) ^ (k + 2) = degreeSign k := by
  rw [degreeSign_succ]
  calc
    _ = degreeSign k * ((-1 : ℤ) ^ k * (-1 : ℤ) ^ (k + 2)) := by ring
    _ = degreeSign k := by
      rw [← pow_add, show k + (k + 2) = 2 * (k + 1) by omega, pow_mul]
      norm_num

/-- 概要：二つの因子と積の座標変換から AW の交差符号が得られる。
方針：次数の和の符号の公式と各符号の平方1を使う。
規約：p と q は切断の前後の chain 次数。
使われ方：HA 1.3.1.13、Kerodon 2.5.9.2（Tag 00SE） の成分の係数 (−1)^(p q)。 -/
lemma degreeSign_cut (p q : ℕ) :
    degreeSign (p + q) * degreeSign p * degreeSign q = (-1 : ℤ) ^ (p * q) := by
  rw [degreeSign_add]
  calc
    _ = (-1 : ℤ) ^ (p * q) *
        (degreeSign p * degreeSign p) * (degreeSign q * degreeSign q) := by ring
    _ = _ := by rw [degreeSign_mul_self, degreeSign_mul_self, mul_one, mul_one]

/-- 概要：符号による二度の座標変換は恒等である。
方針：整数の作用を合成し、符号の平方を消す。
規約：任意の加法可換群で成立する。
使われ方：HA 1.3.1.12 の N4 座標と DK 座標の全次数の同値。 -/
lemma degreeSign_smul_involutive {M : Type*} [AddCommGroup M] (k : ℕ) (x : M) :
    degreeSign k • (degreeSign k • x) = x := by
  rw [← mul_smul, degreeSign_mul_self, one_smul]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
