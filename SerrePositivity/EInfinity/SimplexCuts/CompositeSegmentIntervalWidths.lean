module

public import SerrePositivity.EInfinity.SimplexCuts.ConsecutiveIntervalWidths
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentPositions
public import SerrePositivity.EInfinity.SimplexCuts.CompositeOuterEndpoints
public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrencePosition

/-!
# 元の挿入部分語の区間幅の総和

Berger–Fresse §2.2.3・§2.2.6、M14 L12a の C452。
同じ接頭ブロックの両端を保ち、幅の和を元の外側の両端へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 非空の元の連続区間の幅の和を、同じ両端で読む（BF §2.2.3）。 -/
lemma sum_nonempty_consecutive_intervalWidths {m q : ℕ} (s : Cut m q)
    (a L : ℕ) (hL : 0 < L) (h : a + L ≤ m + 1) :
    (∑ z : Fin L, (hi s ⟨a + z.val, by have hz := z.isLt; omega⟩ -
      lo s ⟨a + z.val, by have hz := z.isLt; omega⟩)) +
      lo s ⟨a, by omega⟩ = hi s ⟨a + (L - 1), by omega⟩ := by
  cases L with
  | zero => omega
  | succ L =>
    simpa only [Nat.add_sub_cancel] using
      sum_consecutive_intervalWidths s a L (by omega)

/-- 元の部分語の両端は、同じ元の接頭ブロックの両端（BF §2.2.6）。 -/
lemma positiveCompositeSegmentPosition_endpoints {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    positiveCompositeSegmentPosition u v k r i ⟨0, r.positive (by omega) i⟩ =
        compositeFirstPosition u v k r (positiveOccurrencePosition u k i) ∧
      positiveCompositeSegmentPosition u v k r i
        ⟨(r.val i).val - 1, by have hp := r.positive (by omega) i; omega⟩ =
        compositeLastPosition u v k r (positiveOccurrencePosition u k i) := by
  constructor
  · apply Fin.ext
    rw [positiveCompositeSegmentPosition_val]
    change compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val + 0 =
      compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val
    omega
  · apply Fin.ext
    rw [positiveCompositeSegmentPosition_val]
    have hs := IntervalCuts.substitute_prefix_length_at_occurrence u v k r i
    change compositePrefixLength u v k r ((Surjection.occurrenceAt u.val k i).val + 1) =
      compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val + (r.val i).val at hs
    change compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val +
        ((r.val i).val - 1) =
      compositePrefixLength u v k r ((Surjection.occurrenceAt u.val k i).val + 1) - 1
    rw [hs]
    have hlen := r.positive (by omega) i
    omega

/-- 同じ挿入部分語の幅の和は、元の外側の両端の差（BF §2.2.6）。 -/
lemma positiveComposite_segment_intervalWidth_sum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    (∑ z : Fin (c.1.val i).val,
      (hi c.2 (positiveCompositeSegmentPosition u v k c.1 i z) -
        lo c.2 (positiveCompositeSegmentPosition u v k c.1 i z))) +
      lo (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i) =
      hi (positiveCompositeOuterCut u v k c) (positiveOccurrencePosition u k i) := by
  have hlen : 0 < (c.1.val i).val := c.1.positive (by omega) i
  let a := compositePrefixLength u v k c.1 (Surjection.occurrenceAt u.val k i).val
  let z0 : Fin (c.1.val i).val := ⟨0, hlen⟩
  let zt : Fin (c.1.val i).val := ⟨(c.1.val i).val - 1, by omega⟩
  have hb : a + (c.1.val i).val ≤ m + n + (d + e) + 1 := by
    have ht := (positiveCompositeSegmentPosition u v k c.1 i zt).isLt
    rw [positiveCompositeSegmentPosition_val] at ht
    change a + ((c.1.val i).val - 1) < m + n + (d + e) + 1 at ht
    omega
  have hw := sum_nonempty_consecutive_intervalWidths c.2 a (c.1.val i).val hlen hb
  have h0 : (⟨a, by omega⟩ : Fin (m + n + (d + e) + 1)) =
      positiveCompositeSegmentPosition u v k c.1 i z0 := by
    apply Fin.ext
    rw [positiveCompositeSegmentPosition_val]
    change a = a + 0
    omega
  rw [h0] at hw
  change (∑ z : Fin (c.1.val i).val,
      (hi c.2 (positiveCompositeSegmentPosition u v k c.1 i z) -
        lo c.2 (positiveCompositeSegmentPosition u v k c.1 i z))) +
      lo c.2 (positiveCompositeSegmentPosition u v k c.1 i z0) =
      hi c.2 (positiveCompositeSegmentPosition u v k c.1 i zt) at hw
  rw [(positiveCompositeSegmentPosition_endpoints u v k c.1 i).1,
    (positiveCompositeSegmentPosition_endpoints u v k c.1 i).2,
    ← (positiveCompositeOuterCut_endpoints u v k c (positiveOccurrencePosition u k i)).1,
    ← (positiveCompositeOuterCut_endpoints u v k c (positiveOccurrencePosition u k i)).2] at hw
  exact hw

end SerrePositivity.EInfinity.SimplexCuts
