module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordAssociativity
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagWordTransport
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendObjects

/-!
# 三重 zigzag の連結の全頂点・全列の結合則

概要：括弧を変更しても、三つの元の zigzag の全頂点と全列を回収する。
方針：元の三部分の列番号を照合し、共有端点の等式を使う。
規約：空語と両接合点を含み、元の射を別の射に置き換えない。
使われ方：全縦射・全単体・余極限上の結合則。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}
  {a b c : Word} {X Y Z V : C}

lemma vertex_assoc (S : Zigzag W a X Y) (T : Zigzag W b Y Z) (U : Zigzag W c Z V)
    (i : Fin ((Word.append (Word.append a b) c).length + 1))
    (j : Fin ((Word.append a (Word.append b c)).length + 1)) (hij : i.val = j.val) :
    (obj (obj S T) U).vertex i = (obj S (obj T U)).vertex j := by
  by_cases ha : i.val ≤ a.length
  · let k : Fin (a.length + 1) := ⟨i.val, by omega⟩
    have hi : Word.leftVertex (Word.append a b) c (Word.leftVertex a b k) = i := Fin.ext rfl
    have hj : Word.leftVertex a (Word.append b c) k = j := Fin.ext hij
    rw [← hi, ← hj]
    exact ((vertex_left (obj S T) U _).trans (vertex_left S T k)).trans
      (vertex_left S (obj T U) k).symm
  · by_cases hb : i.val ≤ a.length + b.length
    · let k : Fin (b.length + 1) := ⟨i.val - a.length, by omega⟩
      have hi : Word.leftVertex (Word.append a b) c (Word.rightVertex a b k) = i :=
        Fin.ext (by dsimp [Word.leftVertex, Word.rightVertex, k]; omega)
      have hj : Word.rightVertex a (Word.append b c) (Word.leftVertex b c k) = j :=
        Fin.ext (by dsimp [Word.leftVertex, Word.rightVertex, k]; omega)
      rw [← hi, ← hj]
      exact ((vertex_left (obj S T) U _).trans (vertex_right S T k)).trans
        ((vertex_right S (obj T U) _).trans (vertex_left T U k)).symm
    · let k : Fin (c.length + 1) := ⟨i.val - (a.length + b.length), by
        have := i.isLt
        change i.val < a.length + b.length + c.length + 1 at this
        omega⟩
      have hi : Word.rightVertex (Word.append a b) c k = i :=
        Fin.ext (by dsimp [Word.rightVertex, k]; omega)
      have hj : Word.rightVertex a (Word.append b c) (Word.rightVertex b c k) = j :=
        Fin.ext (by dsimp [Word.rightVertex, k]; omega)
      rw [← hi, ← hj]
      exact (vertex_right (obj S T) U k).trans
        ((vertex_right S (obj T U) _).trans (vertex_right T U k)).symm

lemma arrow_assoc_heq (S : Zigzag W a X Y) (T : Zigzag W b Y Z) (U : Zigzag W c Z V)
    (i : Fin (Word.append (Word.append a b) c).length)
    (j : Fin (Word.append a (Word.append b c)).length) (hij : i.val = j.val) :
    HEq ((obj (obj S T) U).arrow i) ((obj S (obj T U)).arrow j) := by
  cases i using Fin.addCases with
  | left i =>
    cases i using Fin.addCases with
    | left k =>
      have hj : j = k.castAdd (b.length + c.length) := Fin.ext hij.symm
      subst j
      exact ((arrow_left_heq (obj S T) U _).trans (arrow_left_heq S T k)).trans
        (arrow_left_heq S (obj T U) k).symm
    | right k =>
      have hj : j = (k.castAdd c.length).natAdd a.length := Fin.ext hij.symm
      subst j
      exact ((arrow_left_heq (obj S T) U _).trans (arrow_right_heq S T k)).trans
        ((arrow_right_heq S (obj T U) _).trans (arrow_left_heq T U k)).symm
  | right k =>
    have hj : j = (k.natAdd b.length).natAdd a.length := Fin.ext (by
      change j.val = a.length + (b.length + k.val)
      change a.length + b.length + k.val = j.val at hij
      omega)
    subst j
    exact (arrow_right_heq (obj S T) U k).trans
      ((arrow_right_heq S (obj T U) _).trans (arrow_right_heq T U k)).symm

/-- 三重連結は語の結合等式に沿って元の全対象で一致する。 -/
lemma obj_assoc_heq (S : Zigzag W a X Y) (T : Zigzag W b Y Z) (U : Zigzag W c Z V) :
    HEq (obj (obj S T) U) (obj S (obj T U)) :=
  Zigzag.object_word_hext (Word.append_assoc a b c) _ _
    (vertex_assoc S T U) (arrow_assoc_heq S T U)

end SerrePositivity.EInfinity.Hammock.ZigzagAppend
