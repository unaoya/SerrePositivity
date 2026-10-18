module
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Tactic.NoncommRing

/-!
# 非可換ブロック行列の共役計算の零積模型

概要：二乗零の元による単位と、Lemma 4.16 の共役公式を結合環で証明する。
方針：単位の逆を 1−U と明示し、U²=V²=UV=0 のみで式を展開する。
規約：KST Lemma 4.16 の非可換再記述。VU の順序を保持する。
使われ方：I の単位化上の行列で VU の成分を v_i a と同定する。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：二乗零の元の 1 への和は単位。
方針：逆元 1−U を与えて左右の積を展開する。
規約：KST Lemma 4.16 の補助元、可換性不要。
使われ方：非単位環の単位化上のブロック行列の単位。 -/
def squareZeroUnit (U : R) (hU : U * U = 0) : Rˣ where
  val := 1 + U
  inv := 1 - U
  val_inv := by
    calc
      (1 + U) * (1 - U) = 1 - U * U := by noncomm_ring
      _ = 1 := by rw [hU, sub_zero]
  inv_val := by
    calc
      (1 - U) * (1 + U) = 1 - U * U := by noncomm_ring
      _ = 1 := by rw [hU, sub_zero]

/-- 概要：零積の三条件から Lemma 4.16 の共役公式を得る。
方針：非可換な分配展開で U²、UV、V² の項だけを消す。
規約：KST Lemma 4.16、右乗法に対応する VU の順序。
使われ方：u⁻¹ψ(v)u=ψ(v)φ(v) の実行列の計算。 -/
lemma squareZero_conjugation (U V : R) (hU : U * U = 0)
    (hV : V * V = 0) (hUV : U * V = 0) :
    (1 - U) * (1 + V) * (1 + U) = (1 + V) * (1 + V * U) := by
  calc
    _ = 1 + V + V * U - U * U - U * V - U * V * U := by noncomm_ring
    _ = 1 + V + V * U := by rw [hU, hUV, zero_mul]; simp only [sub_zero]
    _ = (1 + V) * (1 + V * U) := by
      have h : (1 + V) * (1 + V * U) = 1 + V + V * U + V * V * U := by noncomm_ring
      rw [h, hV, zero_mul, add_zero]

/-- 概要：逆向きに零積を持つ二乗零の元の積 VU も二乗零。
方針：結合律で UV を中央にまとめる。
規約：KST Lemma 4.16、非可換ブロックの追加列。
使われ方：右乗法 φ の単位行列への埋め込み。 -/
lemma squareZero_mul_of_reverse_zero (U V : R) (hUV : U * V = 0) :
    (V * U) * (V * U) = 0 := by
  calc
    _ = V * (U * V) * U := by simp only [mul_assoc]
    _ = 0 := by rw [hUV, mul_zero, zero_mul]

/-- 概要：補助単位による共役を単位群内で同定する。
方針：単位の値の外延性から証明済みの共役展開を使う。
規約：KST Lemma 4.16、a を左へ移さず右乗法の順序を保つ。
使われ方：Construction A.6 と μ 版 A.5 の群準同型の端点同定。 -/
lemma squareZeroUnit_conjugation (U V : R) (hU : U * U = 0)
    (hV : V * V = 0) (hUV : U * V = 0) :
    (squareZeroUnit U hU)⁻¹ * squareZeroUnit V hV * squareZeroUnit U hU =
      squareZeroUnit V hV * squareZeroUnit (V * U) (squareZero_mul_of_reverse_zero U V hUV) := by
  apply Units.ext
  exact squareZero_conjugation U V hU hV hUV

end SerrePositivity.KST.ProExcision
