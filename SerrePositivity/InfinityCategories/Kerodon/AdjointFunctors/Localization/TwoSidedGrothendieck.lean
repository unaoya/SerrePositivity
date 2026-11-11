module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat.Op

/-!
# 二方向の Grothendieck 構成の元の三成分

概要：反変・共変 Cat 値関手の二方向の Grothendieck 圏を構成する。
方針：反変側を反対圏の Grothendieck 構成として扱い、その上で共変側を構成する。
規約：対象と射は底・左・右の三成分をそのまま保持する（DK §9.1）。
使われ方：DK §10の hammock graph のホモトピー不変性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Cat.{u, u}) (G : W ⥤ Cat.{u, u})

abbrev contravariantTotal := (Grothendieck (F ⋙ Cat.opFunctor))ᵒᵖ

def contravariantProjection : contravariantTotal F ⥤ W :=
  (Grothendieck.forget (F ⋙ Cat.opFunctor)).op ⋙ (opOpEquivalence W).functor

abbrev total := Grothendieck (contravariantProjection F ⋙ G)

def mk (w : W) (a : F.obj (op w)) (b : G.obj w) : total F G :=
  ⟨op ⟨op w, op a⟩, b⟩

def base (X : total F G) : W := X.base.unop.base.unop

def left (X : total F G) : F.obj (op (base F G X)) := X.base.unop.fiber.unop

def right (X : total F G) : G.obj (base F G X) := X.fiber

def objectEquiv : total F G ≃ (Σ w : W, (F.obj (op w)) × (G.obj w)) where
  toFun X := ⟨base F G X, left F G X, right F G X⟩
  invFun X := mk F G X.1 X.2.1 X.2.2
  left_inv _ := rfl
  right_inv _ := rfl

variable {F G}

def baseMap {X Y : total F G} (f : X ⟶ Y) : base F G X ⟶ base F G Y :=
  f.base.unop.base.unop

def leftMap {X Y : total F G} (f : X ⟶ Y) :
    left F G X ⟶ (F.map (baseMap f).op).toFunctor.obj (left F G Y) :=
  f.base.unop.fiber.unop

def rightMap {X Y : total F G} (f : X ⟶ Y) :
    (G.map (baseMap f)).toFunctor.obj (right F G X) ⟶ right F G Y := f.fiber

def homMk {X Y : total F G} (h : base F G X ⟶ base F G Y)
    (a : left F G X ⟶ (F.map h.op).toFunctor.obj (left F G Y))
    (b : (G.map h).toFunctor.obj (right F G X) ⟶ right F G Y) : X ⟶ Y :=
  { base := Quiver.Hom.op (show Y.base.unop ⟶ X.base.unop from ⟨h.op, a.op⟩)
    fiber := b }

def homEquiv (X Y : total F G) : (X ⟶ Y) ≃
    (Σ h : base F G X ⟶ base F G Y,
      (left F G X ⟶ (F.map h.op).toFunctor.obj (left F G Y)) ×
      ((G.map h).toFunctor.obj (right F G X) ⟶ right F G Y)) where
  toFun f := ⟨baseMap f, leftMap f, rightMap f⟩
  invFun f := homMk f.1 f.2.1 f.2.2
  left_inv _ := rfl
  right_inv _ := rfl

def projection : total F G ⥤ W :=
  Grothendieck.forget _ ⋙ contravariantProjection F

lemma projection_obj (X : total F G) : (projection (F := F) (G := G)).obj X = base F G X := rfl

lemma projection_map {X Y : total F G} (f : X ⟶ Y) :
    (projection (F := F) (G := G)).map f = baseMap f := rfl

lemma baseMap_comp {X Y Z : total F G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseMap (f ≫ g) = baseMap f ≫ baseMap g := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck
