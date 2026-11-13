module

public import SerrePositivity.EInfinity.SimplexCuts.TerminalEquiv

/-!
# 復元した切断の頂点座標

Berger–Fresse §2.2.6–7、M14 L09a R02の証明分割。
接頭部では元の座標、末尾では最後の頂点と順に増える区間番号となる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 接頭部の頂点を復元後の経路へ入れる。 -/
def terminalVertexEmbedding (m q : ℕ) (p : Fin (m + 1))
    (i : Fin (p.val + q + 1)) : Fin (m + (q + 1) + 1) :=
  ⟨i.val, by have hi := i.isLt; have hp := p.isLt; omega⟩

/-- R02の証明分割：接頭部の水平座標は変わらない。 -/
lemma terminalExtend_horizontal_prefix (m q : ℕ) (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (p.val + q + 1)) :
    ((terminalExtend m q p s).horizontal (terminalVertexEmbedding m q p i)).val =
      (s.horizontal i).val := by
  change ((terminalExtend m q p s).val.filter (fun j => j.val < i.val)).card =
    (s.val.filter (fun j => j.val < i.val)).card
  symm
  apply Finset.card_bij (fun j _ => terminalPrefixEmbedding m q p j)
  · intro j hj
    exact Finset.mem_filter.mpr
      ⟨(terminalExtend_mem_prefix m q p s j).mpr (Finset.mem_filter.mp hj).1,
        (Finset.mem_filter.mp hj).2⟩
  · intro j _ k _ h
    exact (terminalPrefixEmbedding m q p).injective h
  · intro j hj
    have hjlt := (Finset.mem_filter.mp hj).2
    have hi := i.isLt
    have hmem := (terminalExtend_mem m q p s j).mp (Finset.mem_filter.mp hj).1
    rcases hmem with ⟨k, hk, he⟩ | he
    · refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩, he⟩
      have hv := congrArg (fun z : Fin (m + (q + 1)) => z.val) he
      change k.val = j.val at hv
      omega
    · change p.val + q < j.val at he
      omega

/-- R02の証明分割：接頭部の垂直座標を一つ大きい有限順序へ入れる。 -/
lemma terminalExtend_vertical_prefix (m q : ℕ) (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (p.val + q + 1)) :
    (terminalExtend m q p s).vertical (terminalVertexEmbedding m q p i) =
      (s.vertical i).castSucc := by
  apply Fin.ext
  have h := (terminalExtend m q p s).coordinate_sum (terminalVertexEmbedding m q p i)
  have h' := s.coordinate_sum i
  rw [terminalExtend_horizontal_prefix] at h
  change (s.horizontal i).val +
    ((terminalExtend m q p s).vertical (terminalVertexEmbedding m q p i)).val = i.val at h
  change _ = (s.vertical i).val
  omega

/-- R02の証明分割：最後の垂直辺の後には全ての垂直辺を通過済み。 -/
lemma terminalExtend_vertical_suffix (m q : ℕ) (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (m + (q + 1) + 1)) (hi : p.val + q < i.val) :
    (terminalExtend m q p s).vertical i = Fin.last (q + 1) := by
  apply Fin.ext
  change ((terminalExtend m q p s).valᶜ.filter (fun j => j.val < i.val)).card = q + 1
  rw [Finset.filter_true_of_mem]
  · exact (terminalExtend m q p s).compl_card
  · intro j hj
    have hj' := le_lastVertical (terminalExtend m q p s) j hj
    rw [lastVertical_terminalExtend] at hj'
    change j.val ≤ p.val + q at hj'
    omega

/-- R02の証明分割：末尾の水平座標は頂点番号からq+1を引いたもの。 -/
lemma terminalExtend_horizontal_suffix (m q : ℕ) (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (m + (q + 1) + 1)) (hi : p.val + q < i.val) :
    ((terminalExtend m q p s).horizontal i).val = i.val - (q + 1) := by
  have h := (terminalExtend m q p s).coordinate_sum i
  rw [terminalExtend_vertical_suffix m q p s i hi] at h
  simp only [Fin.val_last] at h
  omega

end SerrePositivity.EInfinity.SimplexCuts
