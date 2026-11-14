module

public import SerrePositivity.EInfinity.Surjection.OverlapBoundaries

/-!
# 元の重なる分割における水平辺の所属

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の内側射影の証明分割。
元の開始位置が指定位置以下である最後の部分語を使う。
共有端点の位置と、その次へ進む水平辺を区別して読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の開始位置が指定位置以下である部分語の有限集合（BF §1.2.4）。 -/
def segmentEdgeCandidates {t L : ℕ} (r : Surjection.OverlapPartition t L) (p : ℕ) :
    Finset (Fin t) := Finset.univ.filter (fun j => r.start j ≤ p)

/-- C394：元の第零部分語が候補に入る（BF §1.2.4）。 -/
lemma segmentEdgeCandidates_nonempty {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) : (segmentEdgeCandidates r p).Nonempty := by
  refine ⟨⟨0, ht⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  rw [r.start_zero ht]
  exact Nat.zero_le _

/-- 元の有限候補の最後を指定する記法（BF §1.2.4）。 -/
def segmentEdgeOwner {t L : ℕ} (r : Surjection.OverlapPartition t L) (ht : 0 < t) (p : ℕ) :
    Fin t := (segmentEdgeCandidates r p).max' (segmentEdgeCandidates_nonempty r ht p)

/-- C395：指定した元の部分語の開始位置は辺の始点以下（BF §1.2.4）。 -/
lemma segmentEdgeOwner_start_le {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) : r.start (segmentEdgeOwner r ht p) ≤ p :=
  (Finset.mem_filter.mp ((segmentEdgeCandidates r p).max'_mem
    (segmentEdgeCandidates_nonempty r ht p))).2

/-- C396：元の語内の水平辺は、指定した部分語の末尾を越えない（BF §1.2.4）。 -/
lemma segmentEdgeOwner_end_gt {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) (hp : p + 1 < L) :
    p + 1 < r.start (segmentEdgeOwner r ht p) + (r.val (segmentEdgeOwner r ht p)).val := by
  let j := segmentEdgeOwner r ht p
  change p + 1 < r.start j + (r.val j).val
  have hstart := segmentEdgeOwner_start_le r ht p
  have hpos := r.positive (by omega : 0 < L) j
  by_contra hbad
  by_cases hj : j.val + 1 = t
  · have hlast := r.last_end (by omega : 0 < L) j hj
    omega
  · let j' : Fin t := ⟨j.val + 1, by have h := j.isLt; omega⟩
    have hnext := r.start_next j j' rfl
    have hm : j' ∈ segmentEdgeCandidates r p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hle := (segmentEdgeCandidates r p).le_max' j' hm
    change j'.val ≤ j.val at hle
    dsimp only [j'] at hle
    omega

/-- C397：元の始点が進むと、所属部分語の番号は戻らない（BF §1.2.4）。 -/
lemma segmentEdgeOwner_monotone {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (ht : 0 < t) : Monotone (segmentEdgeOwner r ht) := by
  intro p p' hpp'
  apply (segmentEdgeCandidates r p').le_max'
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (segmentEdgeOwner_start_le r ht p).trans hpp'⟩

/-- C398：同じ元の水平辺を含む部分語は、この一つだけ（BF §1.2.4）。 -/
lemma segmentEdgeOwner_unique {t L : ℕ} (r : Surjection.OverlapPartition t L)
    (ht : 0 < t) (p : ℕ) (hp : p + 1 < L) (j : Fin t)
    (hleft : r.start j ≤ p) (hright : p + 1 < r.start j + (r.val j).val) :
    segmentEdgeOwner r ht p = j := by
  let i := segmentEdgeOwner r ht p
  have hl := segmentEdgeOwner_start_le r ht p
  have hr := segmentEdgeOwner_end_gt r ht p hp
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

end SerrePositivity.EInfinity.SimplexCuts
