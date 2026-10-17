module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ClosedHomotopyComposition
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BinaryIntervalTriangles

/-! # Exact internal-Hom units with an arbitrary shared parameter

These unit equations apply to whole interval maps. In particular fixing
a binary interval at its final internal identity gives the original
other interval, with no replacement or Kan filling.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ClosedParameterUnits
variable {T X Y : SSet.{v}}

lemma identity_comp (f : T ⟶ (ihom X).obj Y) :
    lift (toUnit T ≫ MonoidalClosed.id X) f ≫ MonoidalClosed.comp X X Y = f := by
  apply uncurry_injective
  rw [ClosedHomotopyComposition.uncurry_composition,
    ← ClosedParameterComposition.curry_fst X T, uncurry_curry]
  exact ParameterComposition.id_comp _

lemma comp_identity (f : T ⟶ (ihom X).obj Y) :
    lift f (toUnit T ≫ MonoidalClosed.id Y) ≫ MonoidalClosed.comp X Y Y = f := by
  apply uncurry_injective
  rw [ClosedHomotopyComposition.uncurry_composition,
    ← ClosedParameterComposition.curry_fst Y T, uncurry_curry]
  exact ParameterComposition.comp_id _

lemma firstFixed_interval {f₀ f₁ : T ⟶ (ihom X).obj Y} (F : SSet.Homotopy f₀ f₁) :
    (BinaryIntervalTriangles.firstFixed F (MonoidalClosed.comp X X Y)
      (f₁ := toUnit T ≫ MonoidalClosed.id X)).h = F.h := by
  change lift (fst T HomotopyBinarySquare.interval ≫ (toUnit T ≫ MonoidalClosed.id X))
    F.h ≫ MonoidalClosed.comp X X Y = F.h
  have h : fst T HomotopyBinarySquare.interval ≫ (toUnit T ≫ MonoidalClosed.id X) =
      toUnit (T ⊗ HomotopyBinarySquare.interval) ≫ MonoidalClosed.id X := by
    rw [← Category.assoc, comp_toUnit]
  rw [h, identity_comp]

lemma secondFixed_interval {f₀ f₁ : T ⟶ (ihom X).obj Y} (F : SSet.Homotopy f₀ f₁) :
    (BinaryIntervalTriangles.secondFixed F (MonoidalClosed.comp X Y Y)
      (g₁ := toUnit T ≫ MonoidalClosed.id Y)).h = F.h := by
  change lift F.h
    (fst T HomotopyBinarySquare.interval ≫ (toUnit T ≫ MonoidalClosed.id Y)) ≫
      MonoidalClosed.comp X Y Y = F.h
  have h : fst T HomotopyBinarySquare.interval ≫ (toUnit T ≫ MonoidalClosed.id Y) =
      toUnit (T ⊗ HomotopyBinarySquare.interval) ≫ MonoidalClosed.id Y := by
    rw [← Category.assoc, comp_toUnit]
  rw [h, comp_identity]

end SerrePositivity.SimplicialModel.ClosedParameterUnits
