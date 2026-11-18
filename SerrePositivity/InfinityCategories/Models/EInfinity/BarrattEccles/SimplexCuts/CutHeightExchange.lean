module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutHeights
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleExchange

/-!
模型。文献の定義との比較は後で
# 元の水平辺の高さと方向を交換した区間

Berger–Fresse §2.2.3–6、M14 L12a の逆復元。
同じ水平辺の直前・直後の二頂点を使い、元の高さと交換後の両端を照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C421：元の水平辺の高さは、交換した経路の左右の端点で特定される（BF §2.2.6）。 -/
lemma cutHeights_exchange_bounds {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (a : Fin m) (y : Fin (q + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s.exchange y ≤ a.val ↔ y.val ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s a).val) ∧
      (a.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s.exchange y ↔ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s a).val ≤ y.val) := by
  let edge := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHorizontalEdge s a
  let b : Fin (q + m + 1) := Fin.cast (by omega) edge.castSucc
  let c : Fin (q + m + 1) := Fin.cast (by omega) edge.succ
  have hbH : (s.exchange.horizontal b).val = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s a).val := by
    rw [s.exchange_horizontal]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_before_cutHorizontalEdge s a
  have hbV : (s.exchange.vertical b).val = a.val := by
    rw [s.exchange_vertical, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_before_cutHorizontalEdge]
    rfl
  have hstep := s.step_of_mem edge (s.val.orderEmbOfFin_mem s.property a)
  have hcH : (s.exchange.horizontal c).val = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s a).val := by
    rw [s.exchange_horizontal, hstep.2]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_before_cutHorizontalEdge s a
  have hcV : (s.exchange.vertical c).val = a.val + 1 := by
    rw [s.exchange_vertical, hstep.1, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_before_cutHorizontalEdge]
    rfl
  have hbc : c.val = b.val + 1 := rfl
  constructor
  · constructor
    · intro hlo
      by_contra h
      have hlt : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s a).val < y.val := lt_of_not_ge h
      let z := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s.exchange y).min' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s.exchange y)
      have hzH : s.exchange.horizontal z = y := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_lo_vertex s.exchange y
      have hbz : b < z := by
        by_contra hnot
        have hm := s.exchange.horizontal.monotone (le_of_not_gt hnot)
        have hv : (s.exchange.horizontal z).val ≤ (s.exchange.horizontal b).val := hm
        rw [hzH, hbH] at hv
        omega
      have hcz : c ≤ z := by
        change c.val ≤ z.val
        have hval : b.val < z.val := hbz
        omega
      have hm := s.exchange.vertical.monotone hcz
      have hv : (s.exchange.vertical c).val ≤ (s.exchange.vertical z).val := hm
      change (s.exchange.vertical z).val ≤ a.val at hlo
      rw [hcV] at hv
      omega
    · intro hy
      have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_monotone s.exchange (show y ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s a from hy)
      have hb := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_vertical s.exchange (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s a) b (Fin.ext hbH)
      rw [hbV] at hb
      exact hm.trans hb
  · constructor
    · intro hhi
      by_contra h
      have hlt : y.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s a).val := lt_of_not_ge h
      let z := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s.exchange y).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s.exchange y)
      have hzH : s.exchange.horizontal z = y := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex s.exchange y
      have hzb : z ≤ b := by
        by_contra hnot
        have hm := s.exchange.horizontal.monotone (le_of_lt (lt_of_not_ge hnot))
        have hv : (s.exchange.horizontal b).val ≤ (s.exchange.horizontal z).val := hm
        rw [hzH, hbH] at hv
        omega
      have hm := s.exchange.vertical.monotone hzb
      have hv : (s.exchange.vertical z).val ≤ (s.exchange.vertical b).val := hm
      change a.val < (s.exchange.vertical z).val at hhi
      rw [hbV] at hv
      omega
    · intro hy
      have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_monotone s.exchange (show _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s a ≤ y from hy)
      have hc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_le_hi s.exchange (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s a) c (Fin.ext hcH)
      rw [hcV] at hc
      omega

/-- C422：同じ高さの閉区間への所属を、元の交換経路の端点で読む（BF §2.2.6）。 -/
lemma cutHeights_mem_interval {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (a : Fin m)
    (first last : Fin (q + 1)) :
    (first ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s a ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s a ≤ last) ↔
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s.exchange first ≤ a.val ∧ a.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s.exchange last := by
  exact and_congr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights_exchange_bounds s a first).1.symm
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights_exchange_bounds s a last).2.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
