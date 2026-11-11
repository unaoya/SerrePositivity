module

public import Mathlib.CategoryTheory.Category.Cat.Op
public import Mathlib.CategoryTheory.EqToHom

/-!
# 底と両係数を持つ元の二方向図式の圏

概要：底の圏と反変・共変の係数を持つ図式、底と両係数を同時に送る射を構成する。
方針：底の関手を合成し、係数自然変換を同じ底の関手で前合成する。
規約：元の射の恒等・合成則を保持し、弱同値性を入力にしない。
使われ方：DK10.1–10.2の transfunctor の全作用素を束ねる。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram
open CategoryTheory Opposite

structure Data where
  base : Cat.{u, u}
  left : baseᵒᵖ ⥤ Cat.{u, u}
  right : base ⥤ Cat.{u, u}
structure Hom (A B : Data.{u}) where
  base : A.base ⥤ B.base
  left : A.left ⟶ base.op ⋙ B.left
  right : A.right ⟶ base ⋙ B.right
lemma hom_ext {A B : Data.{u}} (f g : Hom A B) (hb : f.base = g.base)
    (hl : HEq f.left g.left) (hr : HEq f.right g.right) : f = g := by
  cases f;cases g;cases hb;cases eq_of_heq hl;cases eq_of_heq hr;rfl

def id (A : Data.{u}) : Hom A A := ⟨𝟭 _, 𝟙 _, 𝟙 _⟩
def comp {A B C : Data.{u}} (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨f.base ⋙ g.base, f.left ≫ Functor.whiskerLeft f.base.op g.left,
    f.right ≫ Functor.whiskerLeft f.base g.right⟩
instance : Category Data.{u} where
  Hom := Hom
  id := id
  comp := comp
  id_comp f := by
    refine hom_ext _ _ rfl ?_ ?_ <;> apply heq_of_eq <;> ext w <;> simp [comp,id]
  comp_id f := by
    refine hom_ext _ _ rfl ?_ ?_ <;> apply heq_of_eq <;> ext w <;> simp [comp,id]
  assoc f g h := by
    refine hom_ext _ _ rfl ?_ ?_ <;> apply heq_of_eq <;> ext w <;> simp [comp,Category.assoc]
@[simp] lemma id_base (A : Data.{u}) : (𝟙 A : A ⟶ A).base = 𝟭 A.base := rfl
@[simp] lemma id_left (A : Data.{u}) : (𝟙 A : A ⟶ A).left = 𝟙 A.left := rfl
@[simp] lemma id_right (A : Data.{u}) : (𝟙 A : A ⟶ A).right = 𝟙 A.right := rfl
@[simp] lemma comp_base {A B C : Data.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).base = f.base ⋙ g.base := rfl
@[simp] lemma comp_left {A B C : Data.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).left = f.left ≫ Functor.whiskerLeft f.base.op g.left := rfl
@[simp] lemma comp_right {A B C : Data.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).right = f.right ≫ Functor.whiskerLeft f.base g.right := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram
