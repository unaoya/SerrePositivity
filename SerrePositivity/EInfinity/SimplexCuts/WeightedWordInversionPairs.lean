module

public import SerrePositivity.EInfinity.SimplexCuts.Signs
public import SerrePositivity.EInfinity.IntervalCuts.InversionCounts

/-!
# 元の語の逆転寄与と区間長の積

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
同じ0/1の寄与の重み付き表示を揃え、両方向の区間長の積を共通にする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の重み付き逆転寄与は、0/1の寄与と同じ両区間長の積（BF §2.2.4）。 -/
lemma weighted_word_inversionTerm_eq {m q r : ℕ} (s : Cut m q)
    (w : Fin (m + 1) → Fin r) (p h : Fin (m + 1)) :
    (if p < h ∧ w h < w p then intervalLength s w p * intervalLength s w h else 0) =
    IntervalCuts.positionInversionTerm w p h * intervalLength s w p * intervalLength s w h := by
  unfold IntervalCuts.positionInversionTerm
  split_ifs <;> simp

/-- 両向きの元の重み付き逆転寄与の区間長の積を揃える（BF §2.2.6）。 -/
lemma weighted_word_inversionPair_eq {m q r : ℕ} (s : Cut m q)
    (w : Fin (m + 1) → Fin r) (p h : Fin (m + 1)) :
    (if p < h ∧ w h < w p then intervalLength s w p * intervalLength s w h else 0) +
      (if h < p ∧ w p < w h then intervalLength s w h * intervalLength s w p else 0) =
    (IntervalCuts.positionInversionTerm w p h + IntervalCuts.positionInversionTerm w h p) *
      intervalLength s w p * intervalLength s w h := by
  rw [weighted_word_inversionTerm_eq, weighted_word_inversionTerm_eq]
  rw [Nat.mul_right_comm (IntervalCuts.positionInversionTerm w h p)
    (intervalLength s w h) (intervalLength s w p), ← Nat.add_mul, ← Nat.add_mul]

end SerrePositivity.EInfinity.SimplexCuts
