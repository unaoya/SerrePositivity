module
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Tactic.Ring
/-!
概要：coherent bar の面・prefix・内部微分に現れる符号を同じ整数単位へ揃える。
方針：二倍の指数を消し、HA の内部点の指数との一致・逆符号を計算する。
規約：標数や係数環に依存せず、整数単位の厳密な等式を示す。
使われ方：正次元列の MC 式の各相殺対の符号。
-/
@[expose] public section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

lemma dgCoherentBar_prefix_prefix_sign (n j : ℤ) :
    n.negOnePow * (n - j).negOnePow = j.negOnePow := by
  rw [← Int.negOnePow_add]
  have h : n + (n - j) = 2 * n + -j := by ring
  rw [h, Int.negOnePow_add, Int.negOnePow_two_mul, Int.negOnePow_neg, one_mul]

lemma dgCoherentBar_prefix_internal_sign (n k j : ℤ) :
    n.negOnePow * (-(n - k)).negOnePow * (k - j).negOnePow = j.negOnePow := by
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  have h : n + -(n - k) + (k - j) = 2 * k + -j := by ring
  rw [h, Int.negOnePow_add, Int.negOnePow_two_mul, Int.negOnePow_neg, one_mul]

lemma dgCoherentBar_face_prefix_sign (n j : ℤ) :
    (n + j).negOnePow * (n - 1).negOnePow = -j.negOnePow := by
  rw [← Int.negOnePow_add]
  have h : n + j + (n - 1) = 2 * (n - 1) + (j + 1) := by ring
  rw [h, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul, Int.negOnePow_succ]

lemma dgCoherentBar_prefix_face_sign (n k j : ℤ) :
    n.negOnePow * (n - k + (j - k)).negOnePow = j.negOnePow := by
  rw [← Int.negOnePow_add]
  have h : n + (n - k + (j - k)) = 2 * (n - k) + j := by ring
  rw [h, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul]

lemma dgCoherentBar_face_face_sign (n i j : ℤ) :
    (n + j).negOnePow * (n - 1 + i).negOnePow =
      -((n + i).negOnePow * (n - 1 + (j - 1)).negOnePow) := by
  rw [← Int.negOnePow_add, ← Int.negOnePow_add]
  have h : n + j + (n - 1 + i) = n + i + (n - 1 + (j - 1)) + 1 := by ring
  rw [h, Int.negOnePow_succ]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
