module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Nat.Choose.Basic

/-!
# 正の周期 Hom と orbit 全複体の座標符号

DAG XIII Construction 2.2.6 の係数模型比較の補助。
群の鎖次数 s に対し ε_s = (-1)^{binom(s,2)} を取る。
同じ Hom 微分と全複体の Koszul 符号の差を、隣接次数の ε の比で補正する。
-/

@[expose] public section
namespace SerrePositivity.EInfinity.PowerOperation

/-- 群の鎖次数に関する指定座標符号。 -/
def cyclicOrbitCoordinateSign (s : ℕ) : ℤˣ := (Nat.choose s 2 : ℤ).negOnePow

lemma cyclicOrbitCoordinateSign_zero : cyclicOrbitCoordinateSign 0 = 1 := by
  simp [cyclicOrbitCoordinateSign]

lemma cyclicOrbitCoordinateSign_succ (s : ℕ) :
    cyclicOrbitCoordinateSign (s + 1) = (s : ℤ).negOnePow * cyclicOrbitCoordinateSign s := by
  simp [cyclicOrbitCoordinateSign, Nat.choose_succ_succ, Int.negOnePow_add]

lemma cyclicOrbitCoordinateSign_sq (s : ℕ) :
    cyclicOrbitCoordinateSign s * cyclicOrbitCoordinateSign s = 1 :=
  Int.units_mul_self _

end SerrePositivity.EInfinity.PowerOperation
