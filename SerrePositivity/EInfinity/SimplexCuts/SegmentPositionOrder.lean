module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentPositionInjective

/-!
# 元の部分語内位置の順序と内側語の位置

Berger–Fresse §1.2.2・§2.2.4–6、M14 L12a のC452。
元の接頭長による順序と、重なる分割の元の共有境界だけを比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の合成位置の順序は、部分語番号と同じ相対位置の辞書式順序（BF §2.2.6）。 -/
lemma positiveCompositeSegmentPosition_lt_iff {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i j : Fin (Surjection.occurrenceCount u.val k))
    (z : Fin (r.val i).val) (w : Fin (r.val j).val) :
    positiveCompositeSegmentPosition u v k r i z < positiveCompositeSegmentPosition u v k r j w ↔
      i < j ∨ (i = j ∧ z.val < w.val) := by
  constructor
  · intro h
    rcases lt_trichotomy i j with hlt | he | hgt
    · exact Or.inl hlt
    · subst j
      refine Or.inr ⟨rfl, ?_⟩
      have hv : (positiveCompositeSegmentPosition u v k r i z).val <
          (positiveCompositeSegmentPosition u v k r i w).val := h
      simp only [positiveCompositeSegmentPosition_val] at hv
      omega
    · have hr : positiveCompositeSegmentPosition u v k r j w <
          positiveCompositeSegmentPosition u v k r i z :=
        IntervalCuts.compositeSegmentPosition_lt u v k r j i hgt w z
      exact False.elim (not_lt_of_ge h.le hr)
  · rintro (h | ⟨he, h⟩)
    · exact IntervalCuts.compositeSegmentPosition_lt u v k r i j h z w
    · subst j
      change compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val + z.val <
        compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val + w.val
      omega

/-- 元の合成位置が進めば、元の内側位置は進むか共有端点として重なる（BF §2.2.6）。 -/
lemma positiveCompositeSegment_future_inner_order {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i j : Fin (Surjection.occurrenceCount u.val k))
    (z : Fin (r.val i).val) (w : Fin (r.val j).val)
    (h : positiveCompositeSegmentPosition u v k r i z <
      positiveCompositeSegmentPosition u v k r j w) :
    r.start i + z.val < r.start j + w.val ∨
      (r.start i + z.val = r.start j + w.val ∧
        z.val + 1 = (r.val i).val ∧ i.val + 1 < Surjection.occurrenceCount u.val k) := by
  rcases (positiveCompositeSegmentPosition_lt_iff u v k r i j z w).mp h with hlt | ⟨he, hzw⟩
  · have hb := r.boundary_mono (by omega : 0 < (n + 1) + e)
      (show i.val + 1 ≤ j.val from hlt)
    rw [r.boundary_next (by omega : 0 < (n + 1) + e) i, r.boundary_at] at hb
    have hz := z.isLt
    have hj := j.isLt
    have hle : r.start i + z.val ≤ r.start j + w.val := by omega
    rcases lt_or_eq_of_le hle with hs | heq
    · exact Or.inl hs
    · exact Or.inr ⟨heq, by omega, by omega⟩
  · subst j
    exact Or.inl (by omega)

end SerrePositivity.EInfinity.SimplexCuts
