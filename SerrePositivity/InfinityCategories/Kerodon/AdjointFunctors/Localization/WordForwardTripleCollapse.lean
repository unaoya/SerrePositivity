module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCut

/-!
# 元の三つの forward 列を一列へ合成する語の射

概要：同じ三列を一つの forward 列へ送る、元の Word 圏の射を構成する。
方針：元の三列番号を零へ送り、全方向と両端の cut を照合する。
規約：元の区間合成を使う WordAction の射である。
使われ方：列内部の指定接頭射・生成矢・残りの合成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse
open CategoryTheory

abbrev word : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ForwardTriple.word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse (word)


lemma direction (i : Fin 3) : word.direction i = .forward := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ForwardTriple.direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse (direction)


def collapse : word ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward where
  orderHom := ⟨fun _ => (0 : Fin 1), fun _ _ _ => le_rfl⟩
  direction_eq i := (direction i).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ForwardTriple.collapse export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse (collapse)


lemma cut_zero : collapse.cut 0 = (0 : Fin 4) := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.cut_zero collapse

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ForwardTriple.cut_zero export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse (cut_zero)


lemma cut_last : collapse.cut (Fin.last 1) = (Fin.last 3 : Fin 4) := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.cut_last collapse

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.ForwardTriple.cut_last export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse (cut_last)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse
