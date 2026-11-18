module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PrefixCaesuras
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.TerminalTrace
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.IntervalExtrema

/-!
模型。文献の定義との比較は後で
# 復元した切断の接頭区間の上下界

Berger–Fresse §2.2.3–4、M14 L09a。
接頭部と末尾の座標の評価から、元の区間のlo・hiの界を運ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C07の証明分割：接頭頂点を逆向きに読む。 -/
def terminalPrefixVertex {m q : ℕ} (p : Fin (m + 1))
    (k : Fin (m + (q + 1) + 1)) (hk : k.val ≤ p.val + q) :
    Fin (p.val + q + 1) := ⟨k.val, by omega⟩

/-- C07の証明分割：接頭部の水平座標の値。 -/
lemma terminal_horizontal_prefix_of_le {m q : ℕ} (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q)
    (k : Fin (m + (q + 1) + 1)) (hk : k.val ≤ p.val + q) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).horizontal k).val =
      (s.horizontal (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefixVertex p k hk)).val :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_horizontal_prefix m q p s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefixVertex p k hk)

/-- C07の証明分割：接頭部の垂直座標の値。 -/
lemma terminal_vertical_prefix_of_le {m q : ℕ} (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q)
    (k : Fin (m + (q + 1) + 1)) (hk : k.val ≤ p.val + q) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).vertical k).val =
      (s.vertical (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefixVertex p k hk)).val :=
  congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_vertical_prefix m q p s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefixVertex p k hk))

/-- C07の証明分割：末尾の区間番号はp以上。 -/
lemma terminal_horizontal_suffix_ge {m q : ℕ} (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q)
    (k : Fin (m + (q + 1) + 1)) (hk : p.val + q < k.val) :
    p.val ≤ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).horizontal k).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_horizontal_suffix m q p s k hk]
  omega

/-- C07：接頭区間のloは、復元した同じ区間の全頂点の下界。 -/
lemma terminal_lo_lower_bound {m q : ℕ} (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q)
    (i : Fin (p.val + 1)) (k : Fin (m + (q + 1) + 1))
    (hc : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).horizontal k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.prefixPosition p i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s i ≤ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).vertical k).val := by
  by_cases hk : k.val ≤ p.val + q
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminal_vertical_prefix_of_le p s k hk]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_vertical
    apply Fin.ext
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminal_horizontal_prefix_of_le p s k hk
    rw [hc] at h
    exact h.symm
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_vertical_suffix m q p s k (lt_of_not_ge hk)]
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_q s i
    simp only [Fin.val_last]
    omega

/-- C08：pより前の区間のhiは、復元後も全頂点の上界。 -/
lemma terminal_hi_upper_bound {m q : ℕ} (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q)
    (i : Fin (p.val + 1)) (hip : i.val < p.val) (k : Fin (m + (q + 1) + 1))
    (hc : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).horizontal k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.prefixPosition p i) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).vertical k).val ≤ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s i := by
  by_cases hk : k.val ≤ p.val + q
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminal_vertical_prefix_of_le p s k hk]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_le_hi
    apply Fin.ext
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminal_horizontal_prefix_of_le p s k hk
    rw [hc] at h
    exact h.symm
  · have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminal_horizontal_suffix_ge p s k (lt_of_not_ge hk)
    rw [hc] at h
    change p.val ≤ i.val at h
    omega

/-- C09：pより後の区間では全ての垂直座標が終点。 -/
lemma terminal_vertical_of_horizontal_gt {m q : ℕ} (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q)
    (i : Fin (m + 1)) (hip : p < i) (k : Fin (m + (q + 1) + 1))
    (hc : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).horizontal k = i) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).vertical k = Fin.last (q + 1) := by
  by_cases hk : k.val ≤ p.val + q
  · have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminal_horizontal_prefix_of_le p s k hk
    rw [hc] at h
    have hb := (s.horizontal (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefixVertex p k hk)).isLt
    change p.val < i.val at hip
    omega
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_vertical_suffix m q p s k (lt_of_not_ge hk)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
