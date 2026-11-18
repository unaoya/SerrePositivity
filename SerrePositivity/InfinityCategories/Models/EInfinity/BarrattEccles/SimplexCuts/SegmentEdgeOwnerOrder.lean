module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SegmentEdgeOwner

/-!
模型。文献の定義との比較は後で
# 元の水平辺の所属番号と同じ開始・終了位置

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の左逆の証明分割。
元の有限候補のmax'と、元の分割の単調な境界を評価する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C442：同じ所属番号より前であることは、元の開始位置で特定できる（BF §1.2.4）。 -/
lemma le_segmentEdgeOwner_iff {t L : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) (i : Fin t) :
    i ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner r ht p ↔ r.start i ≤ p := by
  constructor
  · intro hi
    exact (r.start_mono hi).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_start_le r ht p)
  · intro hi
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeCandidates r p).le_max' i
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

/-- C443：同じ所属番号より後であることは、元の終了位置で特定できる（BF §1.2.4）。 -/
lemma segmentEdgeOwner_le_iff {t L : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) (hp : p + 1 < L) (i : Fin t) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner r ht p ≤ i ↔ p + 1 < r.start i + (r.val i).val := by
  let j := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner r ht p
  have hl : 0 < L := by omega
  constructor
  · intro hji
    have hb := r.boundary_mono hl
      (show j.val + 1 ≤ i.val + 1 from Nat.add_le_add_right hji 1)
    rw [r.boundary_next hl j, r.boundary_next hl i] at hb
    have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_end_gt r ht p hp
    change p + 1 < r.start j + (r.val j).val at hr
    omega
  · intro hr
    by_contra hnot
    have hij : i < j := lt_of_not_ge hnot
    have hb := r.boundary_mono hl (show i.val + 1 ≤ j.val from hij)
    rw [r.boundary_next hl i, r.boundary_at] at hb
    have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_start_le r ht p
    change r.start j ≤ p at hs
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
