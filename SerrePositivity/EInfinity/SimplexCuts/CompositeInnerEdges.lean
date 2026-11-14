module

public import SerrePositivity.EInfinity.SimplexCuts.CompositePrefixLengths
public import SerrePositivity.EInfinity.SimplexCuts.SegmentEdgeOwner

/-!
# 元の内側水平辺の合成語内の位置

Berger–Fresse §2.2.6、M14 L12a の内側射影の証明分割。
所属部分語の元の出現前の接頭長と、同じ辺の部分語内の位置を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C406：指定出現の部分語の終端は元の合成語の全長以下（BF §2.2.6）。 -/
lemma compositePrefixLength_occurrence_end_le {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (j : Fin (Surjection.occurrenceCount u.val k)) :
    compositePrefixLength u v k r (Surjection.occurrenceAt u.val k j).val + (r.val j).val ≤
      m + (n + 1) + (d + e) := by
  have hb := (Surjection.occurrenceAt u.val k j).isLt
  have h := compositePrefixLength_monotone u v k r
    (show (Surjection.occurrenceAt u.val k j).val + 1 ≤ (m + 1) + d by omega)
  rw [compositePrefixLength_full] at h
  change (Surjection.substitute k
    ((List.ofFn u.val).take ((Surjection.occurrenceAt u.val k j).val + 1))
    (r.segments v.val)).length ≤ _ at h
  rw [IntervalCuts.substitute_prefix_length_at_occurrence] at h
  exact h

/-- 同じ所属部分語内の水平辺を、元の合成語の辺位置へ送る（BF §2.2.6）。 -/
def compositeInnerEdge {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (a : Fin (n + e)) : Fin (m + n + (d + e)) :=
  let j := segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) a.val
  ⟨compositePrefixLength u v k r (Surjection.occurrenceAt u.val k j).val +
      (a.val - r.start j), by
    have hl := segmentEdgeOwner_start_le r (Surjection.occurrenceCount_pos u k) a.val
    have hr := segmentEdgeOwner_end_gt r (Surjection.occurrenceCount_pos u k) a.val
      (by have h := a.isLt; omega)
    have hb := compositePrefixLength_occurrence_end_le u v k r j
    change r.start j ≤ a.val at hl
    change a.val + 1 < r.start j + (r.val j).val at hr
    omega⟩

/-- C407：元の内側辺の像は、同じ接頭長と相対位置の和（BF §2.2.6）。 -/
lemma compositeInnerEdge_val {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (a : Fin (n + e)) :
    (compositeInnerEdge u v k r a).val =
      compositePrefixLength u v k r
          (Surjection.occurrenceAt u.val k
            (segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) a.val)).val +
        (a.val - r.start (segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) a.val)) := rfl

/-- C408：元の内側水平辺の像は、合成語内で狭義順序を保つ（BF §2.2.6）。 -/
lemma compositeInnerEdge_strictMono {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    StrictMono (compositeInnerEdge u v k r) := by
  intro a b hab
  let i := segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) a.val
  let j := segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) b.val
  have hij : i ≤ j := segmentEdgeOwner_monotone r
    (Surjection.occurrenceCount_pos u k) (show a.val ≤ b.val from le_of_lt hab)
  have ha := segmentEdgeOwner_start_le r (Surjection.occurrenceCount_pos u k) a.val
  have hb := segmentEdgeOwner_start_le r (Surjection.occurrenceCount_pos u k) b.val
  change r.start i ≤ a.val at ha
  change r.start j ≤ b.val at hb
  change compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val +
      (a.val - r.start i) <
    compositePrefixLength u v k r (Surjection.occurrenceAt u.val k j).val +
      (b.val - r.start j)
  rcases eq_or_lt_of_le hij with he | hlt
  · rw [he] at ha ⊢
    have hv : a.val < b.val := hab
    omega
  · have ho := Surjection.occurrenceAt_strictMono u.val k hlt
    have hpre := compositePrefixLength_monotone u v k r
      (show (Surjection.occurrenceAt u.val k i).val + 1 ≤
        (Surjection.occurrenceAt u.val k j).val from ho)
    change (Surjection.substitute k
      ((List.ofFn u.val).take ((Surjection.occurrenceAt u.val k i).val + 1))
      (r.segments v.val)).length ≤ _ at hpre
    rw [IntervalCuts.substitute_prefix_length_at_occurrence] at hpre
    have hr := segmentEdgeOwner_end_gt r (Surjection.occurrenceCount_pos u k) a.val
      (by have h := a.isLt; omega)
    change a.val + 1 < r.start i + (r.val i).val at hr
    change compositePrefixLength u v k r (Surjection.occurrenceAt u.val k i).val +
      (r.val i).val ≤ compositePrefixLength u v k r
        (Surjection.occurrenceAt u.val k j).val at hpre
    omega

end SerrePositivity.EInfinity.SimplexCuts
