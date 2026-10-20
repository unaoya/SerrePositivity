module

public import SerrePositivity.EInfinity.Hammock.ZigzagAppendAssociativityObjects
public import SerrePositivity.EInfinity.Hammock.ZigzagAppendFunctor
public import Mathlib.CategoryTheory.Products.Associator

/-!
# 元の zigzag の連結関手の結合則

概要：三重連結は、元の語の結合等式による遷移の後で厳密に結合的。
方針：元の全縦射を三部分の頂点番号で照合し、全対象の比較と合わせる。
規約：語の遷移は構成済みの WordAction を使う。
使われ方：graph の全単体と元の余極限上の合成の結合則。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b c : Word} {X Y Z V : C}
  {S S' : Zigzag W a X Y} {T T' : Zigzag W b Y Z} {U U' : Zigzag W c Z V}

lemma app_assoc_heq (f : S ⟶ S') (g : T ⟶ T') (h : U ⟶ U')
    (i : Fin ((Word.append (Word.append a b) c).length + 1))
    (j : Fin ((Word.append a (Word.append b c)).length + 1)) (hij : i.val = j.val) :
    HEq ((map (map f g) h).app i) ((map f (map g h)).app j) := by
  by_cases ha : i.val ≤ a.length
  · let k : Fin (a.length + 1) := ⟨i.val, by omega⟩
    have hi : i = Word.leftVertex (Word.append a b) c (Word.leftVertex a b k) := Fin.ext rfl
    have hj : j = Word.leftVertex a (Word.append b c) k := Fin.ext hij.symm
    exact (((app_index_heq (map f g) h hi).trans (app_left_heq (map f g) h _)).trans
      (app_left_heq f g k)).trans
        ((app_index_heq f (map g h) hj).trans (app_left_heq f (map g h) k)).symm
  · by_cases hb : i.val ≤ a.length + b.length
    · let k : Fin (b.length + 1) := ⟨i.val - a.length, by omega⟩
      have hi : i = Word.leftVertex (Word.append a b) c (Word.rightVertex a b k) :=
        Fin.ext (by dsimp [Word.leftVertex, Word.rightVertex, k]; omega)
      have hj : j = Word.rightVertex a (Word.append b c) (Word.leftVertex b c k) :=
        Fin.ext (by dsimp [Word.leftVertex, Word.rightVertex, k]; omega)
      exact (((app_index_heq (map f g) h hi).trans (app_left_heq (map f g) h _)).trans
        (app_right_heq f g k)).trans
          (((app_index_heq f (map g h) hj).trans (app_right_heq f (map g h) _)).trans
            (app_left_heq g h k)).symm
    · let k : Fin (c.length + 1) := ⟨i.val - (a.length + b.length), by
        have := i.isLt
        change i.val < a.length + b.length + c.length + 1 at this
        omega⟩
      have hi : i = Word.rightVertex (Word.append a b) c k :=
        Fin.ext (by dsimp [Word.rightVertex, k]; omega)
      have hj : j = Word.rightVertex a (Word.append b c) (Word.rightVertex b c k) :=
        Fin.ext (by dsimp [Word.rightVertex, k]; omega)
      exact ((app_index_heq (map f g) h hi).trans (app_right_heq (map f g) h k)).trans
        (((app_index_heq f (map g h) hj).trans (app_right_heq f (map g h) _)).trans
          (app_right_heq g h k)).symm

lemma map_assoc_heq (f : S ⟶ S') (g : T ⟶ T') (h : U ⟶ U') :
    HEq (map (map f g) h) (map f (map g h)) :=
  Zigzag.hom_word_hext (Word.append_assoc a b c) (obj_assoc_heq S T U)
    (obj_assoc_heq S' T' U') _ _ (app_assoc_heq f g h)

/-- 元の連結関手の、全対象・全縦射での厳密な結合則。 -/
lemma functor_assoc :
    (functor (W := W) (a := a) (b := b) (X := X) (Y := Y) (Z := Z)).prod
        (𝟭 (Zigzag W c Z V)) ⋙ functor ⋙ WordAction.functor (eqToHom (Word.append_assoc a b c)) =
      CategoryTheory.prod.associator (Zigzag W a X Y) (Zigzag W b Y Z) (Zigzag W c Z V) ⋙
        (𝟭 (Zigzag W a X Y)).prod functor ⋙ functor := by
  apply Functor.hext (fun p => eq_of_heq
    ((WordAction.obj_eqToHom_heq _ _).trans (obj_assoc_heq p.1.1 p.1.2 p.2)))
  intro p q f
  exact (WordAction.map_eqToHom_heq _ _).trans (map_assoc_heq f.1.1 f.1.2 f.2)

end SerrePositivity.EInfinity.Hammock.ZigzagAppend
