module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyBinarySquare
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ClosedParameterComposition

/-! # Chosen mapping-space intervals compose with the standard closed composition

Simultaneous composition is associative as an equality of whole interval
maps. Its two independent interval parameters give the specified square.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ClosedHomotopyComposition
variable {W X Y Z T : SSet.{v}}

lemma uncurry_composition (f : T ⟶ (ihom X).obj Y) (g : T ⟶ (ihom Y).obj Z) :
    uncurry (lift f g ≫ MonoidalClosed.comp X Y Z) =
      ParameterComposition.comp (uncurry f) (uncurry g) := by
  have h := ClosedParameterComposition.curry_comp (uncurry f) (uncurry g)
  rw [curry_uncurry, curry_uncurry] at h
  rw [← h, uncurry_curry]

variable {f₀ f₁ : T ⟶ (ihom W).obj X} {g₀ g₁ : T ⟶ (ihom X).obj Y}
  {h₀ h₁ : T ⟶ (ihom Y).obj Z}
  (F : SSet.Homotopy f₀ f₁) (G : SSet.Homotopy g₀ g₁) (H : SSet.Homotopy h₀ h₁)

abbrev comp : SSet.Homotopy
    (lift f₀ g₀ ≫ MonoidalClosed.comp W X Y) (lift f₁ g₁ ≫ MonoidalClosed.comp W X Y) :=
  HomotopyBinarySquare.simultaneous F G (MonoidalClosed.comp W X Y)

abbrev square : (T ⊗ HomotopyBinarySquare.interval) ⊗ HomotopyBinarySquare.interval ⟶
    (ihom W).obj Y := HomotopyBinarySquare.square F G (MonoidalClosed.comp W X Y)

lemma assoc_interval : (comp (comp F G) H).h = (comp F (comp G H)).h := by
  apply uncurry_injective
  change uncurry (lift (lift F.h G.h ≫ MonoidalClosed.comp W X Y) H.h ≫
      MonoidalClosed.comp W Y Z) =
    uncurry (lift F.h (lift G.h H.h ≫ MonoidalClosed.comp X Y Z) ≫ MonoidalClosed.comp W X Z)
  rw [uncurry_composition, uncurry_composition, uncurry_composition, uncurry_composition,
    ParameterComposition.assoc]

lemma comp_naturality {U : SSet.{v}} (j : U ⟶ T) :
    (comp (HomotopyClasses.preHomotopy j F) (HomotopyClasses.preHomotopy j G)).h =
      j ▷ HomotopyBinarySquare.interval ≫ (comp F G).h :=
  HomotopyBinarySquare.simultaneous_naturality F G _ j

end SerrePositivity.SimplicialModel.ClosedHomotopyComposition
