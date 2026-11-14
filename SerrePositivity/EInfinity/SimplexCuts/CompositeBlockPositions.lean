module

public import SerrePositivity.EInfinity.SimplexCuts.CompositePrefixLengths

/-!
# 元の外側区間に対応する合成語の最初・最後の位置

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の指定面の照合。
元の代入語の接頭長を使い、同じブロックの位置を読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の空の接頭語の長さは零（BF §1.2.4）。 -/
lemma compositePrefixLength_zero {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    compositePrefixLength u v k r 0 = 0 := rfl

/-- 元の指定外側位置に対応する合成語ブロックの最初の位置（BF §2.2.6）。 -/
def compositeFirstPosition {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) : Fin (m + n + (d + e) + 1) :=
  ⟨compositePrefixLength u v k r p.val, by
    have hs := compositePrefixLength_step u v k r
      (⟨p.val, by have h := p.isLt; omega⟩ : Fin ((m + 1) + d))
    have hm := compositePrefixLength_monotone u v k r
      (show p.val + 1 ≤ (m + 1) + d by have h := p.isLt; omega)
    rw [compositePrefixLength_full] at hm
    change compositePrefixLength u v k r p.val + 1 ≤
      compositePrefixLength u v k r (p.val + 1) at hs
    omega⟩

/-- 元の指定外側位置に対応する合成語ブロックの最後の位置（BF §2.2.6）。 -/
def compositeLastPosition {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) : Fin (m + n + (d + e) + 1) :=
  ⟨compositePrefixLength u v k r (p.val + 1) - 1, by
    have hm := compositePrefixLength_monotone u v k r
      (show p.val + 1 ≤ (m + 1) + d by have h := p.isLt; omega)
    rw [compositePrefixLength_full] at hm
    omega⟩

end SerrePositivity.EInfinity.SimplexCuts
