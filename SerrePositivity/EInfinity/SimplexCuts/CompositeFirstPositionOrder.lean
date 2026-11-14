module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeBlockPositions

/-!
# 同じ合成ブロックの最初の位置の順序

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の元の位置の列挙。
正の部分長で元の接頭長が一以上増える法則を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の外側位置の狭義順序は、同じ合成ブロックの最初の位置の狭義順序（BF §2.2.6）。 -/
lemma compositeFirstPosition_strictMono {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    StrictMono (compositeFirstPosition u v k r) := by
  intro p p' hpp'
  have hs := compositePrefixLength_step u v k r
    (⟨p.val, by have h := p.isLt; omega⟩ : Fin ((m + 1) + d))
  have hm := compositePrefixLength_monotone u v k r
    (show p.val + 1 ≤ p'.val from hpp')
  change compositePrefixLength u v k r p.val + 1 ≤
    compositePrefixLength u v k r (p.val + 1) at hs
  change compositePrefixLength u v k r p.val < compositePrefixLength u v k r p'.val
  omega

end SerrePositivity.EInfinity.SimplexCuts
