module

public import SerrePositivity.EInfinity.Hammock.WordAppend
public import SerrePositivity.EInfinity.Hammock.WordCut

/-!
# 元の三つの forward 列を一列へ合成する語の射

概要：同じ三列を一つの forward 列へ送る、元の Word 圏の射を構成する。
方針：元の三列番号を零へ送り、全方向と両端の cut を照合する。
規約：元の区間合成を使う WordAction の射である。
使われ方：列内部の指定接頭射・生成矢・残りの合成。
-/

@[expose] public section
namespace SerrePositivity.EInfinity.Hammock.Word.ForwardTriple
open CategoryTheory

abbrev word : Word := append (append (single .forward) (single .forward)) (single .forward)

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

def collapse : word ⟶ single .forward where
  orderHom := ⟨fun _ => (0 : Fin 1), fun _ _ _ => le_rfl⟩
  direction_eq i := (direction i).symm

lemma cut_zero : collapse.cut 0 = (0 : Fin 4) := Hom.cut_zero collapse

lemma cut_last : collapse.cut (Fin.last 1) = (Fin.last 3 : Fin 4) := Hom.cut_last collapse

end SerrePositivity.EInfinity.Hammock.Word.ForwardTriple
