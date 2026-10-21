module

public import SerrePositivity.EInfinity.Hammock.WordColumnSplit

/-!
# 内部切断の prefix・残りの語と元の列番号

概要：切断列の内部の前後の一列を含む語の全列を、元の同じ列番号へ照合する。
方針：prefix は零から切断列まで、残りは切断列から最後までの番号を使う。
規約：切断列は forward、前後の空語も含む。
使われ方：元の語の射を切断因子の語へ制限する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word.CutFactor

abbrev prefixWord (w : Word) (i : Fin w.length) : Word :=
  append (ColumnSplit.before w i) (single .forward)

abbrev residualWord (w : Word) (i : Fin w.length) : Word :=
  append (single .forward) (ColumnSplit.after w i)

def prefixColumn (w : Word) (i : Fin w.length) (k : Fin (prefixWord w i).length) :
    Fin w.length := ⟨k.val, by
      have hk := k.isLt
      have hi := i.isLt
      change k.val < i.val + 1 at hk
      omega⟩

def residualColumn (w : Word) (i : Fin w.length) (k : Fin (residualWord w i).length) :
    Fin w.length := ⟨i.val + k.val, by
      have hk := k.isLt
      have hi := i.isLt
      change k.val < 1 + (w.length - i.val - 1) at hk
      omega⟩

lemma prefixColumn_le (w : Word) (i : Fin w.length) (k : Fin (prefixWord w i).length) :
    prefixColumn w i k ≤ i := by
  have hk := k.isLt
  change k.val < i.val + 1 at hk
  exact Nat.le_of_lt_succ hk

lemma le_residualColumn (w : Word) (i : Fin w.length) (k : Fin (residualWord w i).length) :
    i ≤ residualColumn w i k := by change i.val ≤ i.val + k.val; omega

lemma prefix_direction (w : Word) (i : Fin w.length) (hi : w.direction i = .forward)
    (k : Fin (prefixWord w i).length) :
    (prefixWord w i).direction k = w.direction (prefixColumn w i k) := by
  cases k using Fin.addCases with
  | left k =>
    rw [append_direction_left]
    rfl
  | right k =>
    change Fin 1 at k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    rw [append_direction_right]
    exact hi.symm

lemma residual_direction (w : Word) (i : Fin w.length) (hi : w.direction i = .forward)
    (k : Fin (residualWord w i).length) :
    (residualWord w i).direction k = w.direction (residualColumn w i k) := by
  cases k using Fin.addCases with
  | left k =>
    change Fin 1 at k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    rw [append_direction_left]
    exact hi.symm
  | right k =>
    rw [append_direction_right]
    apply congrArg w.direction
    apply Fin.ext
    change i.val + 1 + k.val = i.val + (1 + k.val)
    omega

end SerrePositivity.EInfinity.Hammock.Word.CutFactor
