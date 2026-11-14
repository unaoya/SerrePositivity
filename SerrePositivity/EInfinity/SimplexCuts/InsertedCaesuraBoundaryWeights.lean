module

public import SerrePositivity.EInfinity.SimplexCuts.InsertedCaesura

/-!
# 挿入色の区切りを部分語の末尾と内部で読む

Berger–Fresse §1.2.2・§2.2.4–6、M14 L12a のC452。
元の最後の部分語の末尾は内側語の最後の位置であり、そこには区切りがない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の最後の部分語の末尾は、元の語の区切りではない（BF §1.2.2）。 -/
lemma not_caesura_last_segment_end {t L N : ℕ} (v : Fin L → Fin N)
    (r : Surjection.OverlapPartition t L) (i : Fin t) (z : Fin (r.val i).val)
    (hz : z.val + 1 = (r.val i).val) (hi : i.val + 1 = t) :
    ¬ Surjection.Caesura v (segmentInnerWordPosition r i z) := by
  have hbound := r.start_add_length_le i
  have hpos : 0 < L := by have h := z.isLt; omega
  have hlast := r.last_end hpos i hi
  rintro ⟨a, ha, _⟩
  have hnat : r.start i + z.val < a.val := ha
  have hb := a.isLt
  omega

/-- 元の部分語末尾の挿入区切りは、次の部分語があることと同値（BF §2.2.4）。 -/
lemma positiveComposite_inserted_end_caesura_iff {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val)
    (hz : z.val + 1 = (r.val i).val) :
    Surjection.Caesura (positiveCompositeCutWord u v k r).val
        (positiveCompositeSegmentPosition u v k r i z) ↔
      i.val + 1 < Surjection.occurrenceCount u.val k := by
  constructor
  · intro h
    by_contra hn
    have hi : i.val + 1 = Surjection.occurrenceCount u.val k := by have hb := i.isLt; omega
    rcases (positiveComposite_inserted_caesura_iff u v k r i z).mp h with hv | ⟨_, ht⟩
    · exact not_caesura_last_segment_end v.val r i z hz hi hv
    · omega
  · exact positiveCompositeSegment_boundary_caesura u v k r i z hz

/-- 元の挿入区切りを、部分語末尾と内部で分ける同じ判定式（BF §2.2.4）。 -/
lemma positiveComposite_inserted_caesura_split_iff {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    Surjection.Caesura (positiveCompositeCutWord u v k r).val
        (positiveCompositeSegmentPosition u v k r i z) ↔
      if z.val + 1 = (r.val i).val then i.val + 1 < Surjection.occurrenceCount u.val k
      else Surjection.Caesura v.val (segmentInnerWordPosition r i z) := by
  by_cases hz : z.val + 1 = (r.val i).val
  · rw [ite_eq_left hz]
    exact positiveComposite_inserted_end_caesura_iff u v k r i z hz
  · rw [ite_eq_right hz]
    constructor
    · intro h
      rcases (positiveComposite_inserted_caesura_iff u v k r i z).mp h with hv | ⟨he, _⟩
      · exact hv
      · exact False.elim (hz he)
    · exact positiveCompositeSegment_caesura_of_inner u v k r i z

/-- 同じ元の挿入区切りの0/1重みを、同じ末尾・内部の判定で読む（BF §2.2.4）。 -/
lemma positiveComposite_inserted_caesura_indicator {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (r.val i).val) :
    (if Surjection.Caesura (positiveCompositeCutWord u v k r).val
        (positiveCompositeSegmentPosition u v k r i z) then 1 else 0 : ℕ) =
      if z.val + 1 = (r.val i).val then
        (if i.val + 1 < Surjection.occurrenceCount u.val k then 1 else 0)
      else (if Surjection.Caesura v.val (segmentInnerWordPosition r i z) then 1 else 0) := by
  by_cases hz : z.val + 1 = (r.val i).val
  · simp only [positiveComposite_inserted_caesura_split_iff, ite_eq_left hz]
  · simp only [positiveComposite_inserted_caesura_split_iff, ite_eq_right hz]

/-- 元の挿入区間の符号重みを同じ二つの区切りの場合で読む（BF §2.2.4–6）。 -/
lemma positiveComposite_inserted_intervalLength_formula {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val) :
    intervalLength c.2 (positiveCompositeCutWord u v k c.1).val
        (positiveCompositeSegmentPosition u v k c.1 i z) =
      (hi c.2 (positiveCompositeSegmentPosition u v k c.1 i z) -
        lo c.2 (positiveCompositeSegmentPosition u v k c.1 i z)) +
      (if z.val + 1 = (c.1.val i).val then
        (if i.val + 1 < Surjection.occurrenceCount u.val k then 1 else 0)
      else (if Surjection.Caesura v.val (segmentInnerWordPosition c.1 i z) then 1 else 0)) := by
  unfold intervalLength
  rw [positiveComposite_inserted_caesura_indicator]

end SerrePositivity.EInfinity.SimplexCuts
