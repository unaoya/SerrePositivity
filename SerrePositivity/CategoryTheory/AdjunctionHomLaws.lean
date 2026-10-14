module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # 随伴の転置・逆転置の法則の命題としての公開 -/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace SerrePositivity.AdjunctionHomLaws

open CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)

/-- 転置して逆転置すると元の射になるという法則。 -/
def uncurryCurryLaw {X : C} {Y : D} (f : L.obj X ⟶ Y) : Prop :=
  (a.homEquiv X Y).symm (a.homEquiv X Y f) = f

/-- 逆転置して転置すると元の射になるという法則。 -/
def curryUncurryLaw {X : C} {Y : D} (f : X ⟶ R.obj Y) : Prop :=
  a.homEquiv X Y ((a.homEquiv X Y).symm f) = f

/-- 転置の値域の射に関する自然性の法則。 -/
def curryNaturalityRightLaw {X : C} {Y Z : D} (f : L.obj X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  a.homEquiv X Z (f ≫ g) = a.homEquiv X Y f ≫ R.map g

/-- 転置のパラメータの射に関する自然性の法則。 -/
def curryNaturalityLeftLaw {X Y : C} {Z : D} (f : X ⟶ Y) (g : L.obj Y ⟶ Z) : Prop :=
  a.homEquiv X Z (L.map f ≫ g) = f ≫ a.homEquiv Y Z g

/-- 随伴の転置のパラメータに関する自然性。 -/
lemma curry_naturality_left {X Y : C} {Z : D} (f : X ⟶ Y) (g : L.obj Y ⟶ Z) :
    curryNaturalityLeftLaw a f g := a.homEquiv_naturality_left f g

/-- 随伴の転置・逆転置の左相互逆性。 -/
lemma uncurry_curry {X : C} {Y : D} (f : L.obj X ⟶ Y) : uncurryCurryLaw a f :=
  (a.homEquiv X Y).left_inv f

/-- 随伴の転置・逆転置の右相互逆性。 -/
lemma curry_uncurry {X : C} {Y : D} (f : X ⟶ R.obj Y) : curryUncurryLaw a f :=
  (a.homEquiv X Y).right_inv f

/-- 随伴の転置の値域に関する自然性。 -/
lemma curry_naturality_right {X : C} {Y Z : D} (f : L.obj X ⟶ Y) (g : Y ⟶ Z) :
    curryNaturalityRightLaw a f g := a.homEquiv_naturality_right f g

end SerrePositivity.AdjunctionHomLaws
