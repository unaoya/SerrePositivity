module

public import Mathlib.CategoryTheory.NatIso

/-! # 対象ごとの同型による関手の移送 -/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace SerrePositivity.FunctorTransport

open CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (F : C ⥤ D) (obj : C → D) (e : ∀ X, F.obj X ≅ obj X)

/-- 関手の対象を指定した同型で置き換え、射を比較の順逆で移す。 -/
def transport : C ⥤ D where
  obj := obj
  map {X Y} f := (e X).inv ≫ F.map f ≫ (e Y).hom
  map_id X := by simp
  map_comp f g := by simp

/-- 移送後の関手の対象は指定した対象。 -/
lemma transport_obj (X : C) : (transport F obj e).obj X = obj X := rfl

/-- 移送後の関手の射は比較の順逆との合成。 -/
lemma transport_map {X Y : C} (f : X ⟶ Y) :
    (transport F obj e).map f = (e X).inv ≫ F.map f ≫ (e Y).hom := rfl

/-- 対象ごとの比較は移送後の関手との自然同型になる。 -/
def iso : F ≅ transport F obj e :=
  NatIso.ofComponents e (by
    intro X Y f
    change F.map f ≫ (e Y).hom = (e X).hom ≫ ((e X).inv ≫ F.map f ≫ (e Y).hom)
    simp only [Iso.hom_inv_id_assoc])

/-- 自然比較の順成分は指定した同型の順射。 -/
lemma iso_hom_app (X : C) : (iso F obj e).hom.app X = (e X).hom := rfl

/-- 自然比較の逆成分は指定した同型の逆射。 -/
lemma iso_inv_app (X : C) : (iso F obj e).inv.app X = (e X).inv := rfl

/-- 二変数関手の自然比較は、両変数の射を続けて適用する射と両立する。 -/
@[reassoc]
lemma bimap_naturality {E : Type u₂} [Category.{v₂} E] {H K : C ⥤ D ⥤ E}
    (h : H ≅ K) {A B : C} (f : A ⟶ B) {X Y : D} (g : X ⟶ Y) :
    (H.map f).app X ≫ (H.obj B).map g ≫ (h.hom.app B).app Y =
      (h.hom.app A).app X ≫ (K.map f).app X ≫ (K.obj B).map g := by
  rw [(h.hom.app B).naturality]
  have hh := congrArg (fun k => k.app X) (h.hom.naturality f)
  change (H.map f).app X ≫ (h.hom.app B).app X =
    (h.hom.app A).app X ≫ (K.map f).app X at hh
  rw [← Category.assoc, hh, Category.assoc]

/-- 二変数関手の射を自然比較の順逆で移すと、比較先の二変数の射になる。 -/
lemma bimap_conjugate {E : Type u₂} [Category.{v₂} E] {H K : C ⥤ D ⥤ E}
    (h : H ≅ K) {A B : C} (f : A ⟶ B) {X Y : D} (g : X ⟶ Y) :
    (h.inv.app A).app X ≫ (H.map f).app X ≫ (H.obj B).map g ≫
        (h.hom.app B).app Y =
      (K.map f).app X ≫ (K.obj B).map g := by
  rw [bimap_naturality]
  simp only [← Category.assoc, Iso.inv_hom_id_app_app, Category.id_comp]

end SerrePositivity.FunctorTransport
