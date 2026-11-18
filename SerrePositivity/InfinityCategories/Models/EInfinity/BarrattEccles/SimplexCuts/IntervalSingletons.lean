module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.IntervalExtrema

/-!
模型。文献の定義との比較は後で
# 零長の切断区間と一頂点のfiber

Berger–Fresse §2.2.7、M14 L09a。
係数の文字を削除する境界は、水平座標のfiberが一頂点になる区間から生じる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

lemma lo_le_hi {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (i : Fin (m + 1)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s i ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_vertical s i _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex s i)

/-- C47：区間のfiberが一頂点であることと、両端の垂直座標が一致することは同値。 -/
lemma intervalPositions_card_eq_one_iff {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (i : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).card = 1 ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi, hj, Finset.min'_singleton, Finset.max'_singleton]
  · intro h
    let j₀ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).min' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s i)
    apply Finset.card_eq_one.mpr
    refine ⟨j₀, ?_⟩
    ext j
    constructor
    · intro hj
      apply Finset.mem_singleton.mpr
      have hc := (Finset.mem_filter.mp hj).2
      apply s.vertex_injective
      apply Prod.ext
      · exact hc.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_lo_vertex s i).symm
      · apply Fin.ext
        have h₁ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_vertical s i j hc
        have h₂ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_le_hi s i j hc
        change (s.vertical j).val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s i
        omega
    · intro hj
      exact Finset.mem_singleton.mp hj ▸
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).min'_mem (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s i)

/-- C48：幾何学的長さ零は、一頂点のfiberの条件。 -/
lemma interval_gap_eq_zero_iff {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s i = 0 ↔ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).card = 1 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_card_eq_one_iff]
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_hi s i
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
