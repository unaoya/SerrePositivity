module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapBoundaries

/-!
模型。文献の定義との比較は後で
# 元の重なる分割における水平辺の所属

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の内側射影の証明分割。
元の開始位置が指定位置以下である最後の部分語を使う。
共有端点の位置と、その次へ進む水平辺を区別して読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の開始位置が指定位置以下である部分語の有限集合（BF §1.2.4）。 -/
def segmentEdgeCandidates {t L : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t L) (p : ℕ) :
    Finset (Fin t) := Finset.univ.filter (fun j => r.start j ≤ p)

/-- C394：元の第零部分語が候補に入る（BF §1.2.4）。 -/
lemma segmentEdgeCandidates_nonempty {t L : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeCandidates r p).Nonempty := by
  refine ⟨⟨0, ht⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  rw [r.start_zero ht]
  exact Nat.zero_le _

/-- 元の有限候補の最後を指定する記法（BF §1.2.4）。 -/
def segmentEdgeOwner {t L : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t L) (ht : 0 < t) (p : ℕ) :
    Fin t := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeCandidates r p).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeCandidates_nonempty r ht p)

/-- C395：指定した元の部分語の開始位置は辺の始点以下（BF §1.2.4）。 -/
lemma segmentEdgeOwner_start_le {t L : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) : r.start (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner r ht p) ≤ p :=
  (Finset.mem_filter.mp ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeCandidates r p).max'_mem
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeCandidates_nonempty r ht p))).2

/-- C396：元の語内の水平辺は、指定した部分語の末尾を越えない（BF §1.2.4）。 -/
lemma segmentEdgeOwner_end_gt {t L : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) (hp : p + 1 < L) :
    p + 1 < r.start (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner r ht p) + (r.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner r ht p)).val := by
  let j := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner r ht p
  change p + 1 < r.start j + (r.val j).val
  have hstart := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_start_le r ht p
  have hpos := r.positive (by omega : 0 < L) j
  by_contra hbad
  by_cases hj : j.val + 1 = t
  · have hlast := r.last_end (by omega : 0 < L) j hj
    omega
  · let j' : Fin t := ⟨j.val + 1, by have h := j.isLt; omega⟩
    have hnext := r.start_next j j' rfl
    have hm : j' ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeCandidates r p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hle := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeCandidates r p).le_max' j' hm
    change j'.val ≤ j.val at hle
    dsimp only [j'] at hle
    omega

/-- C397：元の始点が進むと、所属部分語の番号は戻らない（BF §1.2.4）。 -/
lemma segmentEdgeOwner_monotone {t L : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t L)
    (ht : 0 < t) : Monotone (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner r ht) := by
  intro p p' hpp'
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeCandidates r p').le_max'
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_start_le r ht p).trans hpp'⟩

/-- C398：同じ元の水平辺を含む部分語は、この一つだけ（BF §1.2.4）。 -/
lemma segmentEdgeOwner_unique {t L : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) (hp : p + 1 < L) (j : Fin t)
    (hleft : r.start j ≤ p) (hright : p + 1 < r.start j + (r.val j).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner r ht p = j := by
  let i := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner r ht p
  have hl := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_start_le r ht p
  have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.segmentEdgeOwner_end_gt r ht p hp
  rcases lt_trichotomy i j with hij | he | hji
  · have hb := r.boundary_mono (by omega : 0 < L)
      (show i.val + 1 ≤ j.val by have h : i.val < j.val := hij; omega)
    rw [r.boundary_next (by omega : 0 < L) i, r.boundary_at] at hb
    change p + 1 < r.start i + (r.val i).val at hr
    omega
  · exact he
  · have hb := r.boundary_mono (by omega : 0 < L)
      (show j.val + 1 ≤ i.val by have h : j.val < i.val := hji; omega)
    rw [r.boundary_next (by omega : 0 < L) j, r.boundary_at] at hb
    change r.start i ≤ p at hl
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
