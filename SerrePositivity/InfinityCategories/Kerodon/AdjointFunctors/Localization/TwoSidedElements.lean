module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Opposites

/-!
# 元の反変・共変ラベルを持つ二方向の要素圏

概要：底の対象と左右のラベルを持ち、元の全射でラベルを移す要素圏を構成する。
方針：反変側と共変側の元の等式を射の二つの条件として保持する。
規約：ラベルの条件は等式で、底の射や両ラベルを商にしない。
使われ方：DK §9.5・10.6の二方向 bar の元の射列の表示。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Type u) (G : W ⥤ Type u)

structure Element where
  base : W
  left : F.obj (op base)
  right : G.obj base

structure Hom (X Y : Element F G) where
  base : X.base ⟶ Y.base
  left : F.map base.op Y.left = X.left
  right : G.map base X.right = Y.right

@[ext]
lemma hom_ext {X Y : Element F G} (f g : Hom F G X Y) (h : f.base = g.base) : f = g := by
  cases f
  cases g
  cases h
  rfl

def identity (X : Element F G) : Hom F G X X where
  base := 𝟙 X.base
  left := by simp
  right := by simp

def compose {X Y Z : Element F G} (f : Hom F G X Y) (g : Hom F G Y Z) : Hom F G X Z where
  base := f.base ≫ g.base
  left := by
    rw [op_comp, F.map_comp, ConcreteCategory.comp_apply, g.left, f.left]
  right := by
    rw [G.map_comp, ConcreteCategory.comp_apply, f.right, g.right]

instance elementCategory : Category (Element F G) where
  Hom X Y := Hom F G X Y
  id := identity F G
  comp := compose F G
  id_comp f := hom_ext F G _ _ (Category.id_comp f.base)
  comp_id f := hom_ext F G _ _ (Category.comp_id f.base)
  assoc f g h := hom_ext F G _ _ (Category.assoc f.base g.base h.base)

lemma hom_comp_base {X Y Z : Element F G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base := rfl

def projection : Element F G ⥤ W where
  obj X := X.base
  map f := f.base

variable {F G} {F' : Wᵒᵖ ⥤ Type u} {G' : W ⥤ Type u}

def map (α : F ⟶ F') (β : G ⟶ G') : Element F G ⥤ Element F' G' where
  obj X := ⟨X.base, α.app (op X.base) X.left, β.app X.base X.right⟩
  map {X Y} f :=
    { base := f.base
      left := (ConcreteCategory.congr_hom (α.naturality f.base.op) Y.left).symm.trans
        (congrArg (α.app (op X.base)) f.left)
      right := (ConcreteCategory.congr_hom (β.naturality f.base) X.right).symm.trans
        (congrArg (β.app Y.base) f.right) }

lemma map_projection (α : F ⟶ F') (β : G ⟶ G') :
    map α β ⋙ projection F' G' = projection F G := rfl

def elementsFunctor : ((Wᵒᵖ ⥤ Type u) × (W ⥤ Type u)) ⥤ Cat.{u, u} where
  obj FG := Cat.of (Element FG.1 FG.2)
  map αβ := (map αβ.1 αβ.2).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements
