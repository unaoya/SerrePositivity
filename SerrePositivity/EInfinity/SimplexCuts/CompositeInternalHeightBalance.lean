module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentInnerRanks
public import SerrePositivity.EInfinity.SimplexCuts.CompositeOtherActivePrefix
public import SerrePositivity.EInfinity.SimplexCuts.ColorRankActivePrefix
public import SerrePositivity.EInfinity.SimplexCuts.WordCaesuraLengthTransport

/-!
# 同じ部分語の内部辺の高さと外側の順位

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
報告 §289 の高さの釣り合い。同じ辺と同じ色別順位を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ内部辺の順位と先行他色数は、合成の高さと元の区切り順位に一致（BF §2.2.6）。 -/
lemma positiveComposite_segment_internal_height_balance {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin ((c.1.val i).val - 1)) :
    hi (positiveCompositeInnerCut u v k c) (positiveCompositeSegmentInnerPosition u v k c i
        ⟨z.val, by have hz := z.isLt; omega⟩) + positiveCompositeOtherActivePrefix u v k c i =
      hi c.2 (positiveCompositeSegmentPosition u v k c.1 i
        ⟨z.val, by have hz := z.isLt; omega⟩) +
      Surjection.caesuraRank u.val (Surjection.occurrenceAt u.val k i) := by
  let a : Fin (n + e) := ⟨c.1.start i + z.val, by
    have hb := c.1.start_add_length_le i; have hz := z.isLt; omega⟩
  have howner : segmentEdgeOwner c.1 (Surjection.occurrenceCount_pos u k) a.val = i := by
    apply segmentEdgeOwner_unique
    · have hb := a.isLt; omega
    · change c.1.start i ≤ c.1.start i + z.val; omega
    · change c.1.start i + z.val + 1 < c.1.start i + (c.1.val i).val
      have hz := z.isLt; omega
  have hedge : (compositeInnerEdge u v k c.1 a).castSucc =
      positiveCompositeSegmentPosition u v k c.1 i ⟨z.val, by have hz := z.isLt; omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_castSucc, compositeInnerEdge_val, howner,
      positiveCompositeSegmentPosition_val, a, Nat.add_sub_cancel_left]
  let δ := positiveCompositeOuterCut u v k c
  let w := positiveWord u
  let p := positiveOccurrencePosition u k i
  let j := cutHeights (positiveCompositeInnerCut u v k c) a
  let j₀ := colorIntervalFirst δ w k p (positiveOccurrencePosition_value u k i)
  have hm : j ∈ colorIntervalRanks δ w k p := by
    have h := positiveCompositeInnerCut_rank_mem u v k c a
    rw [howner] at h
    exact h
  have hm₀ : j₀ ∈ colorIntervalRanks δ w k p :=
    (colorIntervalRanks δ w k p).min'_mem
      (colorIntervalRanks_nonempty δ w k p (positiveOccurrencePosition_value u k i))
  have hx : δ.horizontal (colorPositionEquiv δ w ⟨k, j⟩) = p :=
    (Finset.mem_filter.mp hm).2
  have hy : δ.horizontal (colorPositionEquiv δ w ⟨k, j₀⟩) = p :=
    (Finset.mem_filter.mp hm₀).2
  have hb := congrArg Finset.card (other_active_prefix_eq_on_interval δ w.val k p
    (positiveOccurrencePosition_value u k i) _ _ hx hy)
  have hr := colorRank_add_other_active_prefix δ w k p j hm
  rw [hb] at hr
  have hv := congrArg (fun x : Fin (q + 1) => x.val)
    (positiveCompositeInnerCut_vertices u v k c a)
  change (vertices δ w k j).val = (cutHeights c.2 (compositeInnerEdge u v k c.1 a)).val at hv
  change (vertices δ w k j).val = hi c.2 (compositeInnerEdge u v k c.1 a).castSucc at hv
  rw [hedge] at hv
  rw [hv] at hr
  have hcaes := caesuraRank_word_eq_mp (by omega : (m + 1) + d = m + d + 1)
    u p (Surjection.occurrenceAt u.val k i) rfl
  change Surjection.caesuraRank w.val p = _ at hcaes
  rw [hcaes] at hr
  exact hr

end SerrePositivity.EInfinity.SimplexCuts
