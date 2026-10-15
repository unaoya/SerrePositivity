module

public import SerrePositivity.HomotopicalAlgebra.Under.ModelCategory
public import SerrePositivity.HomotopicalAlgebra.Quillen.Brown
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Base change for model under categories

Restriction is right Quillen and pushout is left Quillen for every base map.
Ken Brown then preserves weak equivalences between cofibrant under objects.
No left properness is needed for this fixed-base assertion.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.UnderModel
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

instance map_isRightQuillen (f : X ⟶ Y) : Quillen.IsRightQuillen (Under.map f) where
  map_fibrations := fun _ _ _ hp => hp
  map_trivialFibrations := fun _ _ _ hp => hp

instance pushout_isLeftQuillen (f : X ⟶ Y) : Quillen.IsLeftQuillen (Under.pushout f) :=
  Quillen.isLeftQuillen_of_isRightQuillen (Under.mapPushoutAdj f)

/-- The preservation conditions used by Ken Brown; no adjoint is asserted. -/
instance forget_isLeftQuillen (X : C) : Quillen.IsLeftQuillen (Under.forget X) where
  map_cofibrations := fun _ _ _ hp => hp
  map_trivialCofibrations := fun _ _ _ hp => hp

lemma isCofibrant_iff (A : Under X) : IsCofibrant A ↔ Cofibration A.hom := by
  rw [isCofibrant_iff_of_isInitial (Under.mkIdInitial.to A) Under.mkIdInitial,
    cofibrations_under_iff, Under.mkIdInitial_to_right]

lemma pushout_map_weakEquivalence (f : X ⟶ Y) {A B : Under X} (a : A ⟶ B)
    (hA : cofibrations C A.hom) (hB : cofibrations C B.hom)
    (ha : weakEquivalences C a.right) :
    weakEquivalences C ((Under.pushout f).map a).right := by
  have : IsCofibrant A := (isCofibrant_iff A).mpr ⟨hA⟩
  have : IsCofibrant B := (isCofibrant_iff B).mpr ⟨hB⟩
  have : WeakEquivalence a := ⟨ha⟩
  have := Quillen.map_weakEquivalence_of_cofibrant (Under.pushout f) a
  exact mem_weakEquivalences ((Under.pushout f).map a).right

end SerrePositivity.UnderModel
