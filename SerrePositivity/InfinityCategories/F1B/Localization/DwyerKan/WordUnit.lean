module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordAppend

/-!
# 語の連結の左右単位

概要：空語との連結を戻す、元の向きを保つ語の等式を証明する。
方針：長さを同定した後、元の各列の方向を照合する。
規約：等式から得る語の射は元の単調写像を保持する。
使われ方：空語の zigzag による左右単位則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

/-- 語は長さと元の全列の方向で一意に決まる。 -/
lemma object_ext (a b : Word) (h : a.length = b.length)
    (hd : ∀ i : Fin a.length, a.direction i = b.direction (Fin.cast h i)) : a = b := by
  cases a
  cases b
  dsimp only at h
  subst h
  congr
  exact funext hd

lemma empty_append (a : Word) : append empty a = a := by
  apply object_ext (append empty a) a (Nat.zero_add a.length)
  intro i
  let j : Fin a.length := Fin.cast (Nat.zero_add a.length) i
  have hi : j.natAdd 0 = i := Fin.ext (by simp [j])
  exact (congrArg (append empty a).direction hi).symm.trans (append_direction_right empty a j)

lemma append_empty (a : Word) : append a empty = a := by
  apply object_ext (append a empty) a (Nat.add_zero a.length)
  intro i
  let j : Fin a.length := Fin.cast (Nat.add_zero a.length) i
  have hi : j.castAdd 0 = i := Fin.ext rfl
  exact (congrArg (append a empty).direction hi).symm.trans (append_direction_left a empty j)

end SerrePositivity.EInfinity.Hammock.Word
