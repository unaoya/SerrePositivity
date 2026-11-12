module
public import SerrePositivity.HomologicalAlgebra.AlternatingFaceReverse
public import Mathlib.Tactic.Ring

/-!
概要：重みの積 end と通常の Hom 複体の微分を合わせる次数符号。
方針：横次数 n と Hom 次数 q に対し (-1)^(n(q+1)) εₙ を使い、縦横の二つの漸化式を示す。
規約：ε₀=1、εₙ₊₁=(-1)^(n+1)εₙ。負の Hom 次数も許す。
使われ方：HA 1.2.4、G10 の正規化重み end と Dold–Kan Hom 空間の接続。
-/
@[expose] public section
namespace SerrePositivity.HomologicalAlgebra

/-- 横次数 n の end 成分を Hom 次数 q の射に移す符号。 -/
def weightEndHomSign (n : ℕ) (q : ℤ) : ℤˣ :=
  ((n : ℤ) * (q+1)).negOnePow * alternatingFaceReverseSign n

/-- 零横次数の符号は 1。頂点の評価は変わらない。 -/
@[simp] theorem weightEndHomSign_zero (q : ℤ) : weightEndHomSign 0 q = 1 := by
  simp [weightEndHomSign, alternatingFaceReverseSign]

/-- 積全複体の縦微分の符号を通常の Hom 微分に合わせる。 -/
theorem weightEndHomSign_vertical (n : ℕ) (q : ℤ) :
    weightEndHomSign n (q+1) * (n : ℤ).negOnePow = weightEndHomSign n q := by
  unfold weightEndHomSign
  rw [mul_right_comm, ← Int.negOnePow_add]
  have he : (n : ℤ) * (q+1+1) + n = n * (q+1) + 2*n := by ring
  rw [he, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

/-- 重みの微分による横項を通常の Hom 微分の符号に合わせる。 -/
theorem weightEndHomSign_horizontal (n : ℕ) (q : ℤ) :
    weightEndHomSign (n+1) (q+1) = (q+1).negOnePow * weightEndHomSign n q := by
  unfold weightEndHomSign
  rw [alternatingFaceReverseSign]
  simp only [← mul_assoc, ← Int.negOnePow_add]
  have he : ((n+1 : ℕ) : ℤ) * (q+1+1) + (n+1 : ℕ) =
      q+1 + (n : ℤ) * (q+1) + 2*(n+1) := by push_cast; ring
  rw [he, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

/-- 同じ符号を二度掛けると元に戻る。 -/
@[simp] theorem weightEndHomSign_square (n : ℕ) (q : ℤ) :
    weightEndHomSign n q * weightEndHomSign n q = 1 := Int.units_mul_self _

end SerrePositivity.HomologicalAlgebra
