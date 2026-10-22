module

public import SerrePositivity.KST.NonConnective.SequentialSpectrum
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：元の逐次添字と自然数の射列の厳密な対応。
方針：順序圏の射を同じ順序証明で上下に移す。
規約：BF の対象・Hom 宇宙と添字の宇宙を区別する。
使われ方：相対 cofibrant な逐次置換の帰納構成。
-/

@[expose] public section
universe u
open CategoryTheory
namespace SerrePositivity.KST.NonConnective

/-- 元の宇宙に持ち上げた逐次添字から自然数の順序圏へ戻す。 -/
def sequentialIndexDown : SequentialIndex.{u} ⥤ ℕ where
  obj a := a.down
  map f := homOfLE (leOfHom (X := SequentialIndex.{u}) f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- 自然数の順序圏を元の逐次添字へ持ち上げる。 -/
def sequentialIndexUp : ℕ ⥤ SequentialIndex.{u} where
  obj a := ⟨a⟩
  map f := homOfLE (leOfHom (X := ℕ) f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- 元の逐次添字の射は、上下の移動を行っても同じ射に厳密に戻る。 -/
lemma sequentialIndexUpDown_map {a b : SequentialIndex.{u}} (f : a ⟶ b) :
    sequentialIndexUp.map (sequentialIndexDown.map f) = f := Subsingleton.elim _ _

end SerrePositivity.KST.NonConnective
