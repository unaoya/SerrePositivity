module

public import SerrePositivity.EInfinity.Hammock.Word
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# 元の語の長さで制限した全部分圏

概要：長さが n 以下の元の語の全部分圏と、上限を増やす包含を構成する。
方針：元の全色保存単調写像を保持する full subcategory を使う。
規約：次数の上限だけを制限し、全射や単射の射を除かない。
使われ方：Dwyer–Kan §4.2 の長さ濾過。
-/

@[expose] public section
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

def lengthProperty (n : ℕ) : ObjectProperty Word := fun w => w.length ≤ n

abbrev LengthBounded (n : ℕ) := (lengthProperty n).FullSubcategory

def lengthInclusion (n : ℕ) : LengthBounded n ⥤ Word := (lengthProperty n).ι

def lengthBoundInclusion {n m : ℕ} (h : n ≤ m) : LengthBounded n ⥤ LengthBounded m :=
  ObjectProperty.ιOfLE (fun _ hw => hw.trans h)

lemma lengthBoundInclusion_comp {n m : ℕ} (h : n ≤ m) :
    lengthBoundInclusion h ⋙ lengthInclusion m = lengthInclusion n := rfl

end SerrePositivity.EInfinity.Hammock.Word
