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

end SerrePositivity.FunctorTransport
