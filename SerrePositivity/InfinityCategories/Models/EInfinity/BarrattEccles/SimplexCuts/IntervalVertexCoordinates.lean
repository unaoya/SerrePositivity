module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.IntervalExtrema

/-!
模型。文献の定義との比較は後で
# 元の切断区間内の頂点を同じ二座標で読む

Berger–Fresse §2.2.6、M14 L12a の指定面の照合の証明分割。
元のcoordinate_sumで強制される位置番号を、そのまま元の有限経路で読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の経路の二座標の和で決まる位置の記法（BF §2.2.6）。 -/
def coordinatePosition {m q : ℕ} (p : Fin (m + 1)) (c : Fin (q + 1)) : Fin (m + q + 1) :=
  ⟨p.val + c.val, by have hp := p.isLt; have hc := c.isLt; omega⟩

/-- C451a：元の区間内の高さは、同じ経路の指定二座標の頂点（BF §2.2.6）。 -/
lemma coordinates_of_interval {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (p : Fin (m + 1)) (c : Fin (q + 1)) (hl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p ≤ c.val) (hr : c.val ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p) :
    s.horizontal (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition p c) = p ∧ s.vertical (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition p c) = c := by
  let first := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s p).min' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s p)
  let last := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s p).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s p)
  have hfirst := s.coordinate_sum first
  have hlast := s.coordinate_sum last
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_lo_vertex] at hfirst
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex] at hlast
  change p.val + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p = first.val at hfirst
  change p.val + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = last.val at hlast
  have hleft : first ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition p c := by change first.val ≤ p.val + c.val; omega
  have hright : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition p c ≤ last := by change p.val + c.val ≤ last.val; omega
  have hx1 := s.horizontal.monotone hleft
  have hx2 := s.horizontal.monotone hright
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_lo_vertex] at hx1
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex] at hx2
  have hx : s.horizontal (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition p c) = p := le_antisymm hx2 hx1
  refine ⟨hx, Fin.ext ?_⟩
  have hs := s.coordinate_sum (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition p c)
  rw [hx] at hs
  change p.val + (s.vertical (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition p c)).val = p.val + c.val at hs
  omega

/-- C451b：同じ二座標が元の経路上にあることは元の両端で特定できる（BF §2.2.6）。 -/
lemma coordinatePosition_onPath_iff {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (p : Fin (m + 1)) (c : Fin (q + 1)) :
    (s.horizontal (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition p c) = p ∧ s.vertical (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition p c) = c) ↔
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p ≤ c.val ∧ c.val ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p := by
  constructor
  · rintro ⟨hx, hy⟩
    have hl := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_vertical s p (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition p c) hx
    have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_le_hi s p (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinatePosition p c) hx
    simpa only [hy] using And.intro hl hr
  · rintro ⟨hl, hr⟩
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coordinates_of_interval s p c hl hr

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
