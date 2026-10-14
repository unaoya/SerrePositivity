module
public import SerrePositivity.DifferentialGraded.Complexes.Braiding
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.CategoryTheory.Enriched.Opposite
public import Mathlib.Data.ZMod.Basic

/-! # U4 の signed braiding の受入検査と公理監査 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A]
example : SymmetricCategory (Complex A) := inferInstance
example : SymmetricCategory (Complex (ZMod 2)) := inferInstance
example (P Q : Complex A) : β_ P Q = SerrePositivity.cochainTensorSymmetry P Q := rfl
example (D : Type v) [DGCategory A D] : DGCategory A Dᵒᵖ := inferInstance
example (P Q T : Complex A) :
    (α_ P Q T).hom ≫ (β_ P (Q ⊗ T)).hom ≫ (α_ Q T P).hom =
      (β_ P Q).hom ▷ T ≫ (α_ Q P T).hom ≫ Q ◁ (β_ P T).hom :=
  BraidedCategory.hexagon_forward _ _ _
example (P Q T : Complex A) :
    (α_ P Q T).inv ≫ (β_ (P ⊗ Q) T).hom ≫ (α_ T P Q).inv =
      P ◁ (β_ Q T).hom ≫ (α_ P T Q).inv ≫ (β_ P T).hom ▷ Q :=
  BraidedCategory.hexagon_reverse _ _ _
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.signedSwap_naturality
#print axioms SerrePositivity.DifferentialGraded.signedSwap_hexagon_forward
#print axioms SerrePositivity.DifferentialGraded.signedSwap_hexagon_reverse
#print axioms SerrePositivity.DifferentialGraded.complexSymmetricCategory
#print axioms SerrePositivity.DifferentialGraded.braiding_eq_existing
