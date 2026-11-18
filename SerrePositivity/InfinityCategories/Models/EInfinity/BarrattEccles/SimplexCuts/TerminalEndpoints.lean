module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.TerminalIntervalBounds

/-!
模型。文献の定義との比較は後で
# 最後の垂直辺を戻したときの区間端点

Berger–Fresse §2.2.3–4、M14 L09a。
接頭部の左端、最後以外の右端、末尾の定数区間を計算する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C10：接頭区間の左端は変わらない。 -/
lemma lo_terminalExtend_prefix {m q : ℕ} (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q)
    (i : Fin (p.val + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.prefixPosition p i) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s i := by
  let j := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).min' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s i)
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_eq_of_bound _ _ _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalVertexEmbedding m q p j)
  · apply Fin.ext
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_horizontal_prefix]
    exact congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_lo_vertex s i)
  · exact congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_vertical_prefix m q p s j)
  · exact fun k hk => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminal_lo_lower_bound p s i k hk

/-- C11：pより前の接頭区間の右端は変わらない。 -/
lemma hi_terminalExtend_prefix {m q : ℕ} (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q)
    (i : Fin (p.val + 1)) (hip : i.val < p.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.prefixPosition p i) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i := by
  let j := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions s i).max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.intervalPositions_nonempty s i)
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_of_bound _ _ _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalVertexEmbedding m q p j)
  · apply Fin.ext
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_horizontal_prefix]
    exact congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex s i)
  · exact congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_vertical_prefix m q p s j)
  · exact fun k hk => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminal_hi_upper_bound p s i hip k hk

/-- C12：最後の垂直辺の直後の頂点は区間pの右端。 -/
lemma hi_terminalExtend_at {m q : ℕ} (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s) p = q + 1 := by
  let j : Fin (m + (q + 1) + 1) :=
    ⟨p.val + q + 1, by have hp := p.isLt; omega⟩
  have hj : p.val + q < j.val := by change p.val + q < p.val + q + 1; omega
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi_eq_of_bound _ _ _ j
  · apply Fin.ext
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_horizontal_suffix m q p s j hj]
    change p.val + q + 1 - (q + 1) = p.val
    omega
  · exact congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_vertical_suffix m q p s j hj)
  · intro k _
    exact Nat.le_of_lt_succ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).vertical k).isLt

/-- C13：pより後の全区間の両端は終点。 -/
lemma endpoints_terminalExtend_suffix {m q : ℕ} (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q)
    (i : Fin (m + 1)) (hip : p < i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s) i = q + 1 ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s) i = q + 1 := by
  constructor
  · exact congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminal_vertical_of_horizontal_gt p s i hip _
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_lo_vertex _ i))
  · exact congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminal_vertical_of_horizontal_gt p s i hip _
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_hi_vertex _ i))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
