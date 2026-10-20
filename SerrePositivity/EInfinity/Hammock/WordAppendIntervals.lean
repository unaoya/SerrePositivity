module

public import SerrePositivity.EInfinity.Hammock.WordAppendIndices

/-!
# 連結語の左右の同方向区間

概要：左右の部分の同方向区間を、連結語の同じ区間として扱う。
方針：元の列番号の直和への包含と、区間の上下界を照合する。
規約：空区間と接合点を含み、向きの条件を強めない。
使われ方：連結語での同方向区間の合成の回収。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Hammock.Word

lemma leftVertex_mono (a b : Word) {p q : Fin (a.length + 1)} (hpq : p ≤ q) :
    leftVertex a b p ≤ leftVertex a b q := hpq

lemma rightVertex_mono (a b : Word) {p q : Fin (b.length + 1)} (hpq : p ≤ q) :
    rightVertex a b p ≤ rightVertex a b q := Nat.add_le_add_left hpq _

/-- 左の同方向区間の全列は、連結語でも同じ方向。 -/
lemma append_left_direction (a b : Word) (d : Direction) (p q : Fin (a.length + 1))
    (hd : ∀ j : Fin a.length, p.val ≤ j.val → j.val < q.val → a.direction j = d)
    (i : Fin (append a b).length) (hi : (leftVertex a b p).val ≤ i.val)
    (hi' : i.val < (leftVertex a b q).val) : (append a b).direction i = d := by
  have hq := q.isLt
  let j : Fin a.length := ⟨i.val, by change i.val < q.val at hi'; omega⟩
  have hij : i = j.castAdd b.length := Fin.ext rfl
  exact (congrArg (append a b).direction hij).trans
    ((append_direction_left a b j).trans (hd j hi hi'))

/-- 右の同方向区間の全列も、接合点を含めて連結語で同じ方向。 -/
lemma append_right_direction (a b : Word) (d : Direction) (p q : Fin (b.length + 1))
    (hd : ∀ j : Fin b.length, p.val ≤ j.val → j.val < q.val → b.direction j = d)
    (i : Fin (append a b).length) (hi : (rightVertex a b p).val ≤ i.val)
    (hi' : i.val < (rightVertex a b q).val) : (append a b).direction i = d := by
  have hb : i.val < a.length + b.length := i.isLt
  change a.length + p.val ≤ i.val at hi
  change i.val < a.length + q.val at hi'
  let j : Fin b.length := ⟨i.val - a.length, by omega⟩
  have hij : i = j.natAdd a.length := Fin.ext (by dsimp [j]; omega)
  exact (congrArg (append a b).direction hij).trans
    ((append_direction_right a b j).trans (hd j (by dsimp [j]; omega) (by dsimp [j]; omega)))

lemma rightVertex_sub (a b : Word) (p q : Fin (b.length + 1)) :
    (rightVertex a b q).val - (rightVertex a b p).val = q.val - p.val := by
  dsimp [rightVertex]
  omega

end SerrePositivity.EInfinity.Hammock.Word
