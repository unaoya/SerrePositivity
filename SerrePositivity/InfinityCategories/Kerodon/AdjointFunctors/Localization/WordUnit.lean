module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend

/-!
# 語の連結の左右単位

概要：空語との連結を戻す、元の向きを保つ語の等式を証明する。
方針：長さを同定した後、元の各列の方向を照合する。
規約：等式から得る語の射は元の単調写像を保持する。
使われ方：空語の zigzag による左右単位則。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit
open CategoryTheory

/-- 語は長さと元の全列の方向で一意に決まる。 -/
lemma object_ext (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (h : a.length = b.length)
    (hd : ∀ i : Fin a.length, a.direction i = b.direction (Fin.cast h i)) : a = b := by
  cases a
  cases b
  dsimp only at h
  subst h
  congr
  exact funext hd

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit (object_ext)


lemma empty_append (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty a = a := by
  apply object_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty a) a (Nat.zero_add a.length)
  intro i
  let j : Fin a.length := Fin.cast (Nat.zero_add a.length) i
  have hi : j.natAdd 0 = i := Fin.ext (by simp [j])
  exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty a).direction hi).symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty a j)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit (empty_append)


lemma append_empty (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty = a := by
  apply object_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty) a (Nat.add_zero a.length)
  intro i
  let j : Fin a.length := Fin.cast (Nat.add_zero a.length) i
  have hi : j.castAdd 0 = i := Fin.ext rfl
  exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty).direction hi).symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty j)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit (append_empty)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit
