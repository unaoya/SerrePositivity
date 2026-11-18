module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CornerEndpointCoordinates

/-!
模型。文献の定義との比較は後で
# 混合角で変わらない区間の右端

Berger–Fresse §2.2.7、M14 L09a。
垂直辺の始点は区間の最後ではないため、角交換後も一つの区間以外の右端は保存される。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C136：垂直辺の始点は、どの区間の最大頂点でもない。 -/
lemma interval_max_ne_before_vertical {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (b : Fin (m + q))
    (hb : b ∉ s.val) (i : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s i) ≠ b.castSucc := by
  intro he
  have hc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex s i
  rw [he] at hc
  have hn : b.succ ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (s.step_of_notMem b hb).1.trans hc⟩
  have hle := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).le_max' b.succ hn
  rw [he] at hle
  exact (not_le_of_gt b.castSucc_lt_succ) hle

/-- C137：水平から垂直への角交換で、直前の区間以外の右端は変わらない。 -/
lemma hi_swapSteps_hv_of_ne {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (a b : Fin (m + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∉ s.val)
    (i : Fin (m + 1)) (hi : i ≠ s.horizontal a.castSucc) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (s.swapSteps a b) i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i := by
  let j := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s i)
  have hj : j.val ≠ b.val := by
    intro h
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.interval_max_ne_before_vertical s b hb i (Fin.ext h)
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_of_bound _ _ _ j
  · rw [s.horizontal_swapSteps a b hab j hj]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex s i
  · exact congrArg Fin.val (s.vertical_swapSteps a b hab j hj)
  · intro k hk
    have hne : k.val ≠ b.val := by
      intro he
      have he' : k = b.castSucc := Fin.ext he
      rw [he', (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapSteps_hv_coordinates s a b hab ha hb).1] at hk
      exact hi hk.symm
    rw [s.vertical_swapSteps a b hab k hne]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_le_hi s i k
    rw [s.horizontal_swapSteps a b hab k hne] at hk
    exact hk

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
