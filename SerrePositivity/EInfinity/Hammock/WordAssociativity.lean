module

public import SerrePositivity.EInfinity.Hammock.WordUnit

/-!
# 元の語の連結の結合則

概要：三つの語の連結の括弧の変更は、同じ元の列の向きを保つ。
方針：三部分の列番号を照合し、長さと全方向の外延性を使う。
規約：空語を含み、語の等式から得る遷移を後続でも使う。
使われ方：三重 zigzag と graph の結合則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.Word

lemma append_assoc (a b c : Word) : append (append a b) c = append a (append b c) := by
  apply object_ext (append (append a b) c) (append a (append b c))
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

end SerrePositivity.EInfinity.Hammock.Word
