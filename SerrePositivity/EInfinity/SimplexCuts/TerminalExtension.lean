module

public import SerrePositivity.EInfinity.SimplexCuts.LowerPart
public import Mathlib.Order.Interval.Finset.Fin

/-!
# 最後の垂直辺と末尾の水平辺を戻す切断

Berger–Fresse §2.2.6–7、M14 L09a R01の逆向きの構成。
p区間の後で最後の垂直辺を足し、その後の水平辺を全て戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 接頭部の辺位置を元の経路へ入れる。 -/
def terminalPrefixEmbedding (m q : ℕ) (p : Fin (m + 1)) :
    Fin (p.val + q) ↪ Fin (m + (q + 1)) where
  toFun i := ⟨i.val, by have hp := p.isLt; have hi := i.isLt; omega⟩
  inj' i j h := by
    apply Fin.ext
    exact congrArg (fun z : Fin (m + (q + 1)) => z.val) h

/-- 新しく加える最後の垂直辺の位置。 -/
def terminalEdge (m q : ℕ) (p : Fin (m + 1)) : Fin (m + (q + 1)) :=
  ⟨p.val + q, by have hp := p.isLt; omega⟩

/-- R01の逆向き。接頭部の水平辺と、最後の垂直辺より後の全水平辺を取る。 -/
def terminalExtend (m q : ℕ) (p : Fin (m + 1)) (s : Cut p.val q) : Cut m (q + 1) := by
  let e := terminalPrefixEmbedding m q p
  let a := terminalEdge m q p
  have hd : Disjoint (s.val.map e) (Finset.Ioi a) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    obtain ⟨i, _, he⟩ := Finset.mem_map.mp hj
    have hi := i.isLt
    have hj' : a < j := Finset.mem_Ioi.mp hk
    change p.val + q < j.val at hj'
    have he' : i.val = j.val := congrArg Fin.val he
    omega
  refine ⟨s.val.map e ∪ Finset.Ioi a, ?_⟩
  rw [Finset.card_union_of_disjoint hd, Finset.card_map, s.property, Fin.card_Ioi]
  change p.val + (m + (q + 1) - 1 - (p.val + q)) = m
  have hp := p.isLt
  omega

/-- R01の証明分割：復元した水平辺の所属の式。 -/
lemma terminalExtend_mem (m q : ℕ) (p : Fin (m + 1)) (s : Cut p.val q)
    (j : Fin (m + (q + 1))) :
    j ∈ (terminalExtend m q p s).val ↔
      (∃ i ∈ s.val, terminalPrefixEmbedding m q p i = j) ∨ terminalEdge m q p < j := by
  change j ∈ s.val.map (terminalPrefixEmbedding m q p) ∪ Finset.Ioi (terminalEdge m q p) ↔ _
  simp only [Finset.mem_union, Finset.mem_map, Finset.mem_Ioi]

/-- R01の証明分割：接頭部の辺はそのまま復元される。 -/
lemma terminalExtend_mem_prefix (m q : ℕ) (p : Fin (m + 1)) (s : Cut p.val q)
    (i : Fin (p.val + q)) :
    terminalPrefixEmbedding m q p i ∈ (terminalExtend m q p s).val ↔ i ∈ s.val := by
  rw [terminalExtend_mem]
  constructor
  · rintro (⟨j, hj, hji⟩ | h)
    · exact (terminalPrefixEmbedding m q p).injective hji ▸ hj
    · have hi := i.isLt
      change p.val + q < i.val at h
      omega
  · intro hi
    exact Or.inl ⟨i, hi, rfl⟩

/-- R01の証明分割：追加した最後の垂直辺は水平辺集合には入らない。 -/
lemma terminalEdge_not_mem (m q : ℕ) (p : Fin (m + 1)) (s : Cut p.val q) :
    terminalEdge m q p ∉ (terminalExtend m q p s).val := by
  rw [terminalExtend_mem]
  rintro (⟨i, _, hi⟩ | h)
  · have he : i.val = p.val + q := congrArg Fin.val hi
    exact (ne_of_lt i.isLt) he
  · exact (lt_irrefl _) h

/-- R01の証明分割：追加した垂直辺より後は全て水平辺。 -/
lemma terminalExtend_above_mem (m q : ℕ) (p : Fin (m + 1)) (s : Cut p.val q)
    (j : Fin (m + (q + 1))) (hj : terminalEdge m q p < j) :
    j ∈ (terminalExtend m q p s).val :=
  (terminalExtend_mem m q p s j).mpr (Or.inr hj)

end SerrePositivity.EInfinity.SimplexCuts
