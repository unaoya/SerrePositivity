module

public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Factorizations in under categories

This is the dual of `MorphismProperty.HasFactorization.over` in the pinned
Mathlib `CategoryTheory/MorphismProperty/Comma.lean` (Joël Riou, Apache 2.0).
The factorization data itself is Mathlib's existing `MapFactorizationData`.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CategoryTheory.MorphismProperty

/-- Lift a specified factorization of the underlying arrow to `Under S`.
The map from `S` to the intermediate object is the first factor composed
with the structure map of the source. -/
def MapFactorizationData.under {C : Type u} [Category.{v} C]
    {W₁ W₂ : MorphismProperty C} {S : C} {X Y : CategoryTheory.Under S}
    {f : X ⟶ Y} (hf : MapFactorizationData W₁ W₂ f.right) :
    MapFactorizationData W₁.under W₂.under f where
  Z := CategoryTheory.Under.mk (X.hom ≫ hf.i)
  i := CategoryTheory.Under.homMk hf.i
  p := CategoryTheory.Under.homMk hf.p (by simp [CategoryTheory.Under.w f])
  fac := by ext; exact hf.fac
  hi := hf.hi
  hp := hf.hp

/-- Factorizations of any two morphism classes induce factorizations in
the under category, without any model-category hypothesis. -/
instance HasFactorization.under {C : Type u} [Category.{v} C]
    (W₁ W₂ : MorphismProperty C) [W₁.HasFactorization W₂] (S : C) :
    (W₁.under (X := S)).HasFactorization W₂.under where
  nonempty_mapFactorizationData f :=
    ⟨(factorizationData W₁ W₂ f.right).under⟩

end CategoryTheory.MorphismProperty
