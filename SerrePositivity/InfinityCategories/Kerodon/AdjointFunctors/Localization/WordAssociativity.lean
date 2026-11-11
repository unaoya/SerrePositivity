module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit

/-!
# 元の語の連結の結合則

概要：三つの語の連結の括弧の変更は、同じ元の列の向きを保つ。
方針：三部分の列番号を照合し、長さと全方向の外延性を使う。
規約：空語を含み、語の等式から得る遷移を後続でも使う。
使われ方：三重 zigzag と graph の結合則。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

lemma append_assoc (a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) c = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append b c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.object_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) c) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append b c))
    (Nat.add_assoc a.length b.length c.length)
  intro i
  cases i using Fin.addCases with
  | left i =>
    cases i using Fin.addCases with
    | left i =>
      have h : Fin.cast (Nat.add_assoc a.length b.length c.length)
          ((i.castAdd b.length).castAdd c.length) = i.castAdd (b.length + c.length) := Fin.ext rfl
      rw [h]
      simp only [Fin.addCases_left]
    | right i =>
      have h : Fin.cast (Nat.add_assoc a.length b.length c.length)
          ((i.natAdd a.length).castAdd c.length) = (i.castAdd c.length).natAdd a.length :=
        Fin.ext rfl
      rw [h]
      simp only [Fin.addCases_left, Fin.addCases_right]
  | right i =>
    have h : Fin.cast (Nat.add_assoc a.length b.length c.length)
        (i.natAdd (a.length + b.length)) = (i.natAdd b.length).natAdd a.length :=
      Fin.ext (Nat.add_assoc _ _ _)
    rw [h]
    simp only [Fin.addCases_right]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (append_assoc)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
