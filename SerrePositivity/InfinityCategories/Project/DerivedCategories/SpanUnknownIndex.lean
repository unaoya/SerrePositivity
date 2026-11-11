module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanSuffixIndex

/-! # span の標準セルの四つの未知集合

概要：後続の全頂点を含む未知集合は、先頭二点の所属による四種類に限る。
方針：頂点を後続部分と先頭二点に分け、先頭二点の所属で場合分けする。
規約：先頭は A,B または A,C。使われ方：D7 の cofiber の残差方程式の列挙。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

/-- 概要：標準セルの最初の固定頂点。
方針：有限順序集合の零番目を取る。
規約：両セルとも A。使われ方：共通の未知成分の添字。 -/
def spanFirstPrefix (n : ℕ) : Fin (n + 4) := 0

/-- 概要：標準セルの二番目の固定頂点。
方針：値一の有限添字を取る。
規約：左セルでは B、右セルでは C。使われ方：二脚に対応する未知成分。 -/
def spanSecondPrefix (n : ℕ) : Fin (n + 4) := ⟨1, by omega⟩

/-- 概要：標準セルの各頂点は後続部分または先頭二点のいずれか。
方針：値が二以上か、零または一かを判定する。
規約：全ての次元。使われ方：未知集合の四種類への分類。 -/
lemma spanVertex_cases {n : ℕ} (i : Fin (n + 4)) :
    i ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ∨ i = spanFirstPrefix n ∨ i = spanSecondPrefix n := by
  by_cases h : 2 ≤ i.val
  · exact Or.inl ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces i).mpr h)
  · right
    by_cases h' : i.val = 0
    · exact Or.inl (Fin.ext h')
    · right
      apply Fin.ext
      change i.val = 1
      omega

/-- 概要：全後続頂点を含む未知集合は先頭二点の選択による四種類に限る。
方針：頂点の三分法と先頭二点の所属を使い、有限集合の外延性で同定する。
規約：未知集合の大きさへの追加仮定は不要。使われ方：各 dg nerve セルの未知方程式の列挙。 -/
lemma spanUnknown_cases {n : ℕ} (I : Finset (Fin (n + 4)))
    (hI : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ⊆ I) :
    I = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ∨
      I = insert (spanFirstPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) ∨
      I = insert (spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) ∨
      I = insert (spanFirstPrefix n) (insert (spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) := by
  have hm : ∀ i, i ∈ I ↔ i ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n ∨
      (i = spanFirstPrefix n ∧ spanFirstPrefix n ∈ I) ∨
      (i = spanSecondPrefix n ∧ spanSecondPrefix n ∈ I) := by
    intro i
    constructor
    · intro hi
      rcases spanVertex_cases i with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h, h ▸ hi⟩)
      · exact Or.inr (Or.inr ⟨h, h ▸ hi⟩)
    · rintro (hi | ⟨rfl, hi⟩ | ⟨rfl, hi⟩)
      · exact hI hi
      · exact hi
      · exact hi
  by_cases hA : spanFirstPrefix n ∈ I <;> by_cases hB : spanSecondPrefix n ∈ I
  · right; right; right
    ext i
    rw [hm]
    simp only [hA, hB, and_true, Finset.mem_insert]
    tauto
  · right; left
    ext i
    rw [hm]
    simp only [hA, hB, and_true, and_false, or_false, Finset.mem_insert]
    tauto
  · right; right; left
    ext i
    rw [hm]
    simp only [hA, hB, and_true, and_false, false_or, Finset.mem_insert]
    tauto
  · left
    ext i
    rw [hm]
    simp only [hA, hB, and_false, or_false]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
