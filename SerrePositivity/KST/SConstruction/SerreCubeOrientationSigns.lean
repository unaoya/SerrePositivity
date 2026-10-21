module
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Tactic.Linarith

/-! # 元の Serre 立方体と HA の成分の向きの符号
概要：全辺 tensor の向きを、HA の右側頂点数の符号へ移す三角数の符号を構成する。
方針：元の次元について三角数を再帰し、削除と分割の符号を整数の等式で照合する。
規約：次数 −n、右端からの座標。使われ方：元の最高生成元の HA 微分式。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- n 個の辺の向き補正の指数。整数での n(n−1)/2 を元の次元で再帰する。 -/
def serreCubeOrientationExponent : ℕ → ℤ
  | 0 => 0
  | n + 1 => serreCubeOrientationExponent n + (n : ℤ)

/-- 元の向き補正の指数は、三角数の倍として元の次元の二次式を満たす。 -/
lemma serreCubeOrientationExponent_twice (n : ℕ) :
    2 * serreCubeOrientationExponent n = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 2 * (serreCubeOrientationExponent n + (n : ℤ)) =
      ((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) - 1)
    push_cast
    nlinarith [ih]

/-- 元の二ブロックを連結する指数の差は、元の辺の個数の積。 -/
lemma serreCubeOrientationExponent_add (p q : ℕ) :
    serreCubeOrientationExponent (p + q) =
      serreCubeOrientationExponent p + serreCubeOrientationExponent q + (p : ℤ) * (q : ℤ) := by
  have hp := serreCubeOrientationExponent_twice p
  have hq := serreCubeOrientationExponent_twice q
  have hpq := serreCubeOrientationExponent_twice (p + q)
  push_cast at hpq
  nlinarith

/-- 元の最高生成元を HA の成分の向きで読むための符号。 -/
def serreCubeOrientationSign (n : ℕ) : ℤˣ := (serreCubeOrientationExponent n).negOnePow

/-- 元の零次元の向きの補正は恒等。 -/
lemma serreCubeOrientationSign_zero : serreCubeOrientationSign 0 = 1 := by
  exact Int.negOnePow_zero

/-- 元の一段の向きの補正には、元の直前の辺の個数の符号を掛ける。 -/
lemma serreCubeOrientationSign_succ (n : ℕ) :
    serreCubeOrientationSign (n + 1) = serreCubeOrientationSign n * (n : ℤ).negOnePow :=
  Int.negOnePow_add _ _

/-- 元の二ブロックの向きの補正の積との差は、同じ二次数の Koszul 符号。 -/
lemma serreCubeOrientationSign_add (p q : ℕ) :
    serreCubeOrientationSign (p + q) =
      (serreCubeOrientationSign p * serreCubeOrientationSign q) *
        ((p : ℤ) * (q : ℤ)).negOnePow := by
  exact (congrArg Int.negOnePow (serreCubeOrientationExponent_add p q)).trans
    ((Int.negOnePow_add _ _).trans
      (congrArg (fun z => z * ((p : ℤ) * (q : ℤ)).negOnePow) (Int.negOnePow_add _ _)))

/-- 元の右端座標 i の境界係数は、向き補正後に右側頂点数 i+1 の HA の符号になる。 -/
lemma serreCubeOrientationSign_boundary (n : ℕ) (i : ℤ) :
    serreCubeOrientationSign (n + 1) * ((n : ℤ) - i).negOnePow =
      -((i + 1).negOnePow * serreCubeOrientationSign n) := by
  rw [serreCubeOrientationSign_succ, Int.negOnePow_sub]
  have hs : (n : ℤ).negOnePow * (n : ℤ).negOnePow = 1 := Int.units_mul_self _
  rw [← mul_assoc, mul_assoc (serreCubeOrientationSign n), hs, mul_one]
  rw [Int.negOnePow_add, Int.negOnePow_one]
  simp only [mul_neg, mul_one, neg_mul, neg_neg, mul_comm]

end SerrePositivity.KST.SConstruction
