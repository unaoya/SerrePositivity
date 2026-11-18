module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.TerminalSuffix

/-!
模型。文献の定義との比較は後で
# 最後の垂直辺で分けた頂点列

Berger–Fresse §2.2.6–7、M14 L09a R02の証明分割。
同じ復元切断の頂点列を、接頭部と末尾に分けて評価する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- R02の証明分割：復元した切断の色付き頂点列の接頭部と末尾。 -/
lemma terminalExtend_trace {m q r : ℕ} (v : Fin (m + 1) → Fin r)
    (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q) :
    List.ofFn (fun i =>
      (v ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).horizontal i), (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).vertical i)) =
    (List.ofFn (fun i => ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.prefixLabels v p) (s.horizontal i),
      (s.vertical i).castSucc))) ++
    List.ofFn (fun j : Fin (m - p.val + 1) =>
      (v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalSuffixIndex p j), Fin.last (q + 1))) := by
  have hn : m + (q + 1) + 1 = (p.val + q + 1) + (m - p.val + 1) := by
    have hp := p.isLt
    omega
  rw [List.ofFn_congr hn, List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn
    funext i
    apply Prod.ext
    · exact congrArg v (Fin.ext (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_horizontal_prefix m q p s i))
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_vertical_prefix m q p s i
  · apply congrArg List.ofFn
    funext j
    have hj : p.val + q <
        (Fin.cast hn.symm (j.natAdd (p.val + q + 1))).val := by
      change p.val + q < p.val + q + 1 + j.val
      omega
    apply Prod.ext
    · apply congrArg v
      apply Fin.ext
      have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_horizontal_suffix m q p s
        (Fin.cast hn.symm (j.natAdd (p.val + q + 1))) hj
      change _ = p.val + j.val
      simp only [Fin.val_cast, Fin.val_natAdd] at h
      omega
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_vertical_suffix m q p s _ hj

/-- R02。欠けた色は空のリスト、末尾の重複は出現回数だけの反復として保持する。 -/
lemma verticesList_lastVertical {m q r : ℕ} (v : Fin (m + 1) → Fin r)
    (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q) (c : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutLastVerticalEquiv m q).symm ⟨p, s⟩) v c =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.prefixLabels v p) c).map Fin.castSucc ++
      List.replicate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalMultiplicity v p c) (Fin.last (q + 1)) := by
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s) v c = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList_eq_selectColor, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_trace, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor_append,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor_terminalSuffix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList_eq_selectColor]
  congr 1
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor_map]
  rw [List.map_ofFn]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
