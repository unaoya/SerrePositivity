module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanPrefixIndex

/-! # cospan の標準セルの未知集合

概要：先頭の全頂点を含む未知集合は末尾の二点の選択による四種類に限る。
方針：頂点を先頭の集合と末尾の二点に分け、有限集合の所属で場合分けする。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：二セルの四成分ずつから共通二成分を同定する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：標準セルの末尾の二点の最初の点。
方針：先頭の n+2 点の直後の番号を取る。
規約：HTT §1.2.13、左セルでは B、右セルでは C。使われ方：未知の脚側の成分の添字。 -/
def cospanFirstTail (n : ℕ) : Fin (n + 4) := ⟨n + 2, by omega⟩

/-- 概要：標準セルの最後の点。
方針：有限順序集合の最後の番号を取る。
規約：HTT §1.2.13、両セルとも D。使われ方：共通の未知成分の添字。 -/
def cospanLastTail (n : ℕ) : Fin (n + 4) := Fin.last (n + 3)

/-- 概要：標準セルの各頂点は先頭の集合または末尾の二点のいずれか。
方針：番号の上界と先頭の所属条件から残る二値を判定する。
規約：HTT §1.2.13。使われ方：未知集合の四種類への分類。 -/
lemma cospanVertex_cases {n : ℕ} (i : Fin (n + 4)) :
    i ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ∨ i = cospanFirstTail n ∨ i = cospanLastTail n := by
  by_cases h : i.val < n + 2
  · exact Or.inl ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_cospanPrefixFaces i).mpr h)
  · right
    have hi := i.isLt
    by_cases h' : i.val = n + 2
    · exact Or.inl (Fin.ext h')
    · right
      apply Fin.ext
      change i.val = n + 3
      omega

/-- 概要：未知集合は先頭の集合と末尾の二点を選んで加えた四種類に限る。
方針：先頭の包含と頂点の三分法を使い、末尾の二点の所属で四つに分ける。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：各セルで検証すべき未知方程式の列挙。 -/
lemma cospanUnknown_cases {n : ℕ} (I : Finset (Fin (n + 4)))
    (hI : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ⊆ I) :
    I = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ∨
      I = insert (cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) ∨
      I = insert (cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) ∨
      I = insert (cospanFirstTail n) (insert (cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) := by
  have hm : ∀ i, i ∈ I ↔ i ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n ∨
      (i = cospanFirstTail n ∧ cospanFirstTail n ∈ I) ∨
      (i = cospanLastTail n ∧ cospanLastTail n ∈ I) := by
    intro i
    constructor
    · intro hi
      rcases cospanVertex_cases i with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h, h ▸ hi⟩)
      · exact Or.inr (Or.inr ⟨h, h ▸ hi⟩)
    · rintro (hi | ⟨rfl, hi⟩ | ⟨rfl, hi⟩)
      · exact hI hi
      · exact hi
      · exact hi
  by_cases hB : cospanFirstTail n ∈ I <;> by_cases hD : cospanLastTail n ∈ I
  · right; right; right
    ext i
    rw [hm]
    simp only [hB, hD, and_true, Finset.mem_insert]
    tauto
  · right; left
    ext i
    rw [hm]
    simp only [hB, hD, and_true, and_false, or_false, Finset.mem_insert]
    tauto
  · right; right; left
    ext i
    rw [hm]
    simp only [hB, hD, and_true, and_false, false_or, Finset.mem_insert]
    tauto
  · left
    ext i
    rw [hm]
    simp only [hB, hD, and_false, or_false]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
