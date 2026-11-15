module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalVertexKinds

/-!
# 水平境界と零長区間

Berger–Fresse §2.2.7、M14 L09a。
係数の一文字を削除する境界が、一頂点の区間を消す操作であることを有限条件で表す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C61：水平な隣接辺の条件は、水平座標のfiberが一頂点である条件。 -/
lemma horizontalVertex_iff_card_eq_one {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) :
    HorizontalVertex s k ↔ (intervalPositions s (s.horizontal k)).card = 1 := by
  rw [← horizontal_fiber_singleton_iff]
  constructor
  · intro h
    apply Finset.card_eq_one.mpr
    refine ⟨k, ?_⟩
    ext j
    simp only [intervalPositions, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact ⟨fun hj => h j hj, fun hj => hj ▸ rfl⟩
  · intro h
    obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp h
    have hk : k = j₀ := by
      apply Finset.mem_singleton.mp
      rw [← hj₀]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    intro j hj
    have he : j = j₀ := by
      apply Finset.mem_singleton.mp
      rw [← hj₀]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    exact he.trans hk.symm

/-- C62：水平境界は、正の総次数で指定区間が零長になる場合。 -/
lemma boundaryVertexKind_eq_horizontal_gap {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) :
    boundaryVertexKind s k = .horizontal ↔
      0 < m + q ∧ hi s (s.horizontal k) - lo s (s.horizontal k) = 0 := by
  rw [boundaryVertexKind_eq_horizontal_iff, interval_gap_eq_zero_iff,
    horizontalVertex_iff_card_eq_one]

/-- C63：水平境界があれば、消す水平次数が正である。 -/
lemma horizontal_kind_pos {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (hk : boundaryVertexKind s k = .horizontal) : 0 < m := by
  obtain ⟨hN, hh⟩ := (boundaryVertexKind_eq_horizontal_iff s k).mp hk
  have hm : s.val.Nonempty := by
    by_cases h0 : k.val = 0
    · have he : k = 0 := Fin.ext h0
      rw [he, horizontalVertex_zero_iff s hN] at hh
      exact ⟨_, hh⟩
    · let a : Fin (m + q) := ⟨k.val - 1, by have hb := k.isLt; omega⟩
      have ha : a.succ = k := by apply Fin.ext; change k.val - 1 + 1 = k.val; omega
      exact ⟨a, hh.1 a ha⟩
  simpa only [s.property] using Finset.card_pos.mpr hm

end SerrePositivity.EInfinity.SimplexCuts
