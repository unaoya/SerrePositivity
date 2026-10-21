module

public import SerrePositivity.EInfinity.SimplicialLocalization.GeneratorBlockComposition
public import Mathlib.CategoryTheory.Equivalence

/-!
# 交互標準形の圏と元の自由圏

概要：交互標準形を射とする圏は、元の Paths C と同じ対象上で圏同値である。
方針：正規化と flatten の互いに逆な全単射と、元の連結との両立を使う。
規約：対象の変更や恒等文字の削除をしない。
使われ方：元の hammock の各行を交互標準形で扱うための圏。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization.GeneratorBlocks
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

def BlockCategory (_W : MorphismProperty C) := C

instance category : Category.{max u v} (BlockCategory W) where
  Hom X Y := Normal W X Y
  id X := empty W X
  comp N M := comp W N M
  id_comp := empty_comp W
  comp_id := comp_empty W
  assoc := comp_assoc W

def flattenFunctor : BlockCategory W ⥤ Paths C where
  obj X := X
  map N := flattenNormal W N
  map_id _ := rfl
  map_comp N M := flatten_comp W N M

def normalizeFunctor : Paths C ⥤ BlockCategory W where
  obj X := X
  map p := normalize W p
  map_id _ := rfl
  map_comp p q := normalize_comp W p q

def categoryEquivalence : BlockCategory W ≌ Paths C where
  functor := flattenFunctor W
  inverse := normalizeFunctor W
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y N
    change comp W N (empty W Y) =
      comp W (empty W X) (normalize W (flattenNormal W N))
    rw [comp_empty, empty_comp, normalize_flattenNormal])
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y p
    change flattenNormal W (normalize W p) ≫ 𝟙 _ = 𝟙 _ ≫ p
    rw [flatten_normalize, Category.comp_id, Category.id_comp])
  functor_unitIso_comp X := rfl

end SerrePositivity.EInfinity.SimplicialLocalization.GeneratorBlocks
