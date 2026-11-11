module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPostcompose

/-!
# 元の始域比較の二つの行の語の挿入

概要：元の二つの三列表示を同じ四列 −+−+ へ送る。
方針：元の列を保つ単射と全 cut を明示する。
規約：上行は中央、下行は先頭に恒等 backward を挿入する。
使われ方：source frame 比較の始域自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords
open CategoryTheory

def word : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := ⟨4, ![.backward, .forward, .backward, .forward]⟩
abbrev preWord : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word

def upperInsert : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postWord ⟶ word where
  orderHom := ⟨(![0, 1, 3] : Fin 3 → Fin 4), by decide⟩
  direction_eq i := by fin_cases i <;> rfl

def lowerInsert : preWord ⟶ word where
  orderHom := ⟨(![1, 2, 3] : Fin 3 → Fin 4), by decide⟩
  direction_eq i := by fin_cases i <;> rfl

lemma upperInsert_cut (j : Fin 5) : upperInsert.cut j = (![0, 1, 2, 2, 3] : Fin 5 → Fin 4) j := by
  fin_cases j <;> decide

lemma lowerInsert_cut (j : Fin 5) : lowerInsert.cut j = (![0, 0, 1, 2, 3] : Fin 5 → Fin 4) j := by
  fin_cases j <;> decide

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords
