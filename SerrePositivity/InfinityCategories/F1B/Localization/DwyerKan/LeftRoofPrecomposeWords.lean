module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.LeftRoofPostcompose

/-!
# 元の始域比較の二つの行の語の挿入

概要：元の二つの三列表示を同じ四列 −+−+ へ送る。
方針：元の列を保つ単射と全 cut を明示する。
規約：上行は中央、下行は先頭に恒等 backward を挿入する。
使われ方：source frame 比較の始域自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose
open CategoryTheory

def word : Word := ⟨4, ![.backward, .forward, .backward, .forward]⟩
abbrev preWord : Word := Word.append (Word.single .forward) LeftRoof.word

def upperInsert : LeftRoof.postWord ⟶ word where
  orderHom := ⟨(![0, 1, 3] : Fin 3 → Fin 4), by decide⟩
  direction_eq i := by fin_cases i <;> rfl

def lowerInsert : preWord ⟶ word where
  orderHom := ⟨(![1, 2, 3] : Fin 3 → Fin 4), by decide⟩
  direction_eq i := by fin_cases i <;> rfl

lemma upperInsert_cut (j : Fin 5) : upperInsert.cut j = (![0, 1, 2, 2, 3] : Fin 5 → Fin 4) j := by
  fin_cases j <;> decide

lemma lowerInsert_cut (j : Fin 5) : lowerInsert.cut j = (![0, 0, 1, 2, 3] : Fin 5 → Fin 4) j := by
  fin_cases j <;> decide

end SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose
