module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.TerminalEquiv

/-!
模型。文献の定義との比較は後で
# 復元した切断の頂点座標

Berger–Fresse §2.2.6–7、M14 L09a R02の証明分割。
接頭部では元の座標、末尾では最後の頂点と順に増える区間番号となる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 接頭部の頂点を復元後の経路へ入れる。 -/
def terminalVertexEmbedding (m q : ℕ) (p : Fin (m + 1))
    (i : Fin (p.val + q + 1)) : Fin (m + (q + 1) + 1) :=
  ⟨i.val, by have hi := i.isLt; have hp := p.isLt; omega⟩

/-- R02の証明分割：接頭部の水平座標は変わらない。 -/
lemma terminalExtend_horizontal_prefix (m q : ℕ) (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q)
    (i : Fin (p.val + q + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).horizontal (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalVertexEmbedding m q p i)).val =
      (s.horizontal i).val := by
  change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).val.filter (fun j => j.val < i.val)).card =
    (s.val.filter (fun j => j.val < i.val)).card
  symm
  apply Finset.card_bij (fun j _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefixEmbedding m q p j)
  · intro j hj
    exact Finset.mem_filter.mpr
      ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_mem_prefix m q p s j).mpr (Finset.mem_filter.mp hj).1,
        (Finset.mem_filter.mp hj).2⟩
  · intro j _ k _ h
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalPrefixEmbedding m q p).injective h
  · intro j hj
    have hjlt := (Finset.mem_filter.mp hj).2
    have hi := i.isLt
    have hmem := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_mem m q p s j).mp (Finset.mem_filter.mp hj).1
    rcases hmem with ⟨k, hk, he⟩ | he
    · refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩, he⟩
      have hv := congrArg (fun z : Fin (m + (q + 1)) => z.val) he
      change k.val = j.val at hv
      omega
    · change p.val + q < j.val at he
      omega

/-- R02の証明分割：接頭部の垂直座標を一つ大きい有限順序へ入れる。 -/
lemma terminalExtend_vertical_prefix (m q : ℕ) (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q)
    (i : Fin (p.val + q + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).vertical (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalVertexEmbedding m q p i) =
      (s.vertical i).castSucc := by
  apply Fin.ext
  have h := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).coordinate_sum (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalVertexEmbedding m q p i)
  have h' := s.coordinate_sum i
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_horizontal_prefix] at h
  change (s.horizontal i).val +
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).vertical (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalVertexEmbedding m q p i)).val = i.val at h
  change _ = (s.vertical i).val
  omega

/-- R02の証明分割：最後の垂直辺の後には全ての垂直辺を通過済み。 -/
lemma terminalExtend_vertical_suffix (m q : ℕ) (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q)
    (i : Fin (m + (q + 1) + 1)) (hi : p.val + q < i.val) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).vertical i = Fin.last (q + 1) := by
  apply Fin.ext
  change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).valᶜ.filter (fun j => j.val < i.val)).card = q + 1
  rw [Finset.filter_true_of_mem]
  · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).compl_card
  · intro j hj
    have hj' := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.le_lastVertical (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s) j hj
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lastVertical_terminalExtend] at hj'
    change j.val ≤ p.val + q at hj'
    omega

/-- R02の証明分割：末尾の水平座標は頂点番号からq+1を引いたもの。 -/
lemma terminalExtend_horizontal_suffix (m q : ℕ) (p : Fin (m + 1)) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut p.val q)
    (i : Fin (m + (q + 1) + 1)) (hi : p.val + q < i.val) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).horizontal i).val = i.val - (q + 1) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend m q p s).coordinate_sum i
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.terminalExtend_vertical_suffix m q p s i hi] at h
  simp only [Fin.val_last] at h
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
