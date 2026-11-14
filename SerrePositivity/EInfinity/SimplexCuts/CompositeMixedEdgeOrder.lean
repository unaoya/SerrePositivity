module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeInnerEdges

/-!
# 元の外側境界と内側内部辺の混合した順序

Berger–Fresse §2.2.6、M14 L12a の逆復元の証明分割。
元の接頭長と指定出現の部分長を保ち、両種の辺が交わらないことを読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C427：内側辺と外側境界の順序は、元の所属出現の位置で決まる（BF §2.2.6）。 -/
lemma compositeInnerOuterEdge_order {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (a : Fin (n + e)) (i : Fin (m + d)) :
    ((Surjection.occurrenceAt u.val k
        (segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) a.val)).val ≤ i.val →
      compositeInnerEdge u v k r a < compositeOuterEdge u v k r i) ∧
    (i.val < (Surjection.occurrenceAt u.val k
        (segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) a.val)).val →
      compositeOuterEdge u v k r i < compositeInnerEdge u v k r a) := by
  let j := segmentEdgeOwner r (Surjection.occurrenceCount_pos u k) a.val
  let p := (Surjection.occurrenceAt u.val k j).val
  have hl := segmentEdgeOwner_start_le r (Surjection.occurrenceCount_pos u k) a.val
  have hr := segmentEdgeOwner_end_gt r (Surjection.occurrenceCount_pos u k) a.val
    (by have h := a.isLt; omega)
  change r.start j ≤ a.val at hl
  change a.val + 1 < r.start j + (r.val j).val at hr
  have hnext : compositePrefixLength u v k r (p + 1) =
      compositePrefixLength u v k r p + (r.val j).val :=
    IntervalCuts.substitute_prefix_length_at_occurrence u v k r j
  constructor
  · intro hp
    have hm := compositePrefixLength_monotone u v k r
      (show p + 1 ≤ i.val + 1 by change p ≤ i.val at hp; omega)
    change compositePrefixLength u v k r p + (a.val - r.start j) <
      compositePrefixLength u v k r (i.val + 1) - 1
    omega
  · intro hp
    have hm := compositePrefixLength_monotone u v k r
      (show i.val + 1 ≤ p by change i.val < p at hp; omega)
    let i' : Fin ((m + 1) + d) := ⟨i.val, by have h := i.isLt; omega⟩
    have hs := compositePrefixLength_step u v k r i'
    change compositePrefixLength u v k r i.val + 1 ≤
      compositePrefixLength u v k r (i.val + 1) at hs
    change compositePrefixLength u v k r (i.val + 1) - 1 <
      compositePrefixLength u v k r p + (a.val - r.start j)
    omega

end SerrePositivity.EInfinity.SimplexCuts
