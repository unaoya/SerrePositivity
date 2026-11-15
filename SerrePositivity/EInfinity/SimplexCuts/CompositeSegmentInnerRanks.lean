module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentVertexRanks
public import SerrePositivity.EInfinity.SimplexCuts.CompositeInnerRankBounds
public import SerrePositivity.EInfinity.SimplexCuts.ColorIntervalVertexOrder

/-!
# 元の挿入部分語の全頂点は同じ内側切断に属する

Berger–Fresse §2.2.6、M14 L12a の指定頂点の照合。
元の辺の所属と、同じ色別区間内の高さの順序を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ内側位置は部分語の開始と相対位置の和（BF §2.2.6）。 -/
def positiveCompositeSegmentInnerPosition {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val) :
    Fin (n + e + 1) :=
  ⟨c.1.start i + z.val, by
    have h := c.1.start_add_length_le i; have hz := z.isLt; omega⟩

/-- 同じ外側順位は元の所属出現の区間内（BF §2.2.6）。 -/
lemma positiveCompositeSegmentVertexRank_mem {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
    positiveCompositeSegmentVertexRank u v k c i z x hx ∈
      colorIntervalRanks (positiveCompositeOuterCut u v k c) (positiveWord u) k
        (positiveOccurrencePosition u k i) :=
  colorHeightRank_mem _ _ _ _ _ _ _ _

/-- 元の挿入頂点の同じ順位は、内側Cutの元の両端の間（BF §2.2.6）。 -/
lemma positiveCompositeSegmentRank_inner_bounds {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z) :
    lo (positiveCompositeInnerCut u v k c) (positiveCompositeSegmentInnerPosition u v k c i z) ≤
        (positiveCompositeSegmentVertexRank u v k c i z x hx).val ∧
      (positiveCompositeSegmentVertexRank u v k c i z x hx).val ≤
        hi (positiveCompositeInnerCut u v k c)
          (positiveCompositeSegmentInnerPosition u v k c i z) := by
  let j := positiveCompositeSegmentInnerPosition u v k c i z
  let rank := positiveCompositeSegmentVertexRank u v k c i z x hx
  have hm := positiveCompositeSegmentVertexRank_mem u v k c i z x hx
  have hj : j.val = c.1.start i + z.val := rfl
  have hz := z.isLt
  have hb := c.1.start_add_length_le i
  change lo (positiveCompositeInnerCut u v k c) j ≤ rank.val ∧
    rank.val ≤ hi (positiveCompositeInnerCut u v k c) j
  constructor
  · by_cases hj0 : j.val = 0
    · have he : j = 0 := Fin.ext hj0
      rw [he, lo_zero]
      exact Nat.zero_le _
    · let a : Fin (n + e) := ⟨j.val - 1, by have h := j.isLt; omega⟩
      have hja : j = a.succ := Fin.ext (by dsimp only [a]; simp only [Fin.val_succ]; omega)
      have ha : a.val + 1 = j.val := by dsimp only [a]; omega
      rw [hja, ← hi_eq_lo_succ]
      change (cutHeights (positiveCompositeInnerCut u v k c) a).val ≤ rank.val
      let owner := segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val
      have ho : owner ≤ i := (segmentEdgeOwner_le_iff c.1
        (Surjection.occurrenceCount_pos u k) a.val (by have h := a.isLt; omega) i).mpr (by omega)
      have heMem := positiveCompositeInnerCut_rank_mem u v k c a
      rcases eq_or_lt_of_le ho with he | hlt
      · have heOwner : segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val = i := he
        rw [heOwner] at heMem
        have hePos : (compositeInnerEdge u v k c.1 a).succ =
            positiveCompositeSegmentPosition u v k c.1 i z := by
          apply Fin.ext
          simp only [Fin.val_succ, compositeInnerEdge_val, heOwner,
            positiveCompositeSegmentPosition_val]
          have hs := segmentEdgeOwner_start_le c.1 (Surjection.occurrenceCount_pos u k) a.val
          rw [heOwner] at hs
          omega
        have hheight := lo_le_vertical c.2 (compositeInnerEdge u v k c.1 a).succ x
          (hx.trans hePos.symm)
        rw [← hi_eq_lo_succ] at hheight
        apply (vertices_le_iff_on_colorInterval _ _ _ _
          (positiveOccurrencePosition_value u k i) _ _ heMem hm).mp
        rw [positiveCompositeInnerCut_vertices, positiveCompositeSegmentVertexRank_vertices]
        exact hheight
      · exact le_of_lt (colorIntervalRanks_ordered _ _ _ _ _
          (positiveOccurrencePosition_strictMono u k hlt) _ _ heMem hm)
  · by_cases hjlast : j.val = n + e
    · have he : j = Fin.last (n + e) := Fin.ext hjlast
      rw [he, hi_last]
      exact Nat.le_of_lt_succ rank.isLt
    · let a : Fin (n + e) := ⟨j.val, by have h := j.isLt; omega⟩
      have hja : j = a.castSucc := Fin.ext rfl
      have ha : a.val = j.val := rfl
      rw [hja]
      change rank.val ≤ (cutHeights (positiveCompositeInnerCut u v k c) a).val
      let owner := segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val
      have ho : i ≤ owner := (le_segmentEdgeOwner_iff c.1
        (Surjection.occurrenceCount_pos u k) a.val i).mpr (by omega)
      have heMem := positiveCompositeInnerCut_rank_mem u v k c a
      rcases eq_or_lt_of_le ho with he | hlt
      · have heOwner :
            segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val = i := he.symm
        rw [heOwner] at heMem
        have hePos : (compositeInnerEdge u v k c.1 a).castSucc =
            positiveCompositeSegmentPosition u v k c.1 i z := by
          apply Fin.ext
          simp only [Fin.val_castSucc, compositeInnerEdge_val, heOwner,
            positiveCompositeSegmentPosition_val]
          omega
        have hheight := vertical_le_hi c.2 (compositeInnerEdge u v k c.1 a).castSucc x
          (hx.trans hePos.symm)
        apply (vertices_le_iff_on_colorInterval _ _ _ _
          (positiveOccurrencePosition_value u k i) _ _ hm heMem).mp
        rw [positiveCompositeSegmentVertexRank_vertices, positiveCompositeInnerCut_vertices]
        exact hheight
      · exact le_of_lt (colorIntervalRanks_ordered _ _ _ _ _
          (positiveOccurrencePosition_strictMono u k hlt) _ _ hm heMem)

end SerrePositivity.EInfinity.SimplexCuts
