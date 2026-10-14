module
public import SerrePositivity.HomologicalAlgebra.FaithfullyFlatDerivedHomology

/-! # Homology descent over each power residue ring

Only the residue rings are faithfully flat. The original algebra need not be flat.
The input objects already live over the residue ring; comparison with Koszul cones is separate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable {R : Type u} [CommRing R] (a : R) (S : Type u) [CommRing S] [Algebra R S]
variable (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) S) (k : ℕ)
include hS
local notation "A" => R ⧸ Ideal.span {a ^ k}
local notation "B" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {a ^ k})

/-- The standard map between the actual power residue rings is faithfully flat, including k=0. -/
lemma powerResidueRingHom_faithfullyFlat : (algebraMap A B).FaithfullyFlat := by
  have := faithfullyFlat_power_algebraQuotient_of_completelyFaithfullyFlat a S hS k
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr this

/-- Derived scalar extension between the actual power residue rings. -/
def powerResidueDerivedBaseChange :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  flatDerivedBaseChange (algebraMap A B) (powerResidueRingHom_faithfullyFlat a S hS k).flat

/-- All-degree homology base change over the actual residue rings, natural in all derived maps. -/
def powerResidueDerivedHomologyNatIso (n : ℤ) :
    powerResidueDerivedBaseChange a S hS k ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} B) n ≅
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ⋙
        ModuleCat.extendScalars (algebraMap A B) :=
  flatDerivedBaseChangeHomologyNatIso _ (powerResidueRingHom_faithfullyFlat a S hS k).flat n

/-- Zero homology maps descend at every finite stage. -/
lemma powerResidueDerivedHomology_map_eq_zero_iff (n : ℤ)
    {X Y : DerivedCategory (ModuleCat.{u} A)} (f : X ⟶ Y) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).map
        ((powerResidueDerivedBaseChange a S hS k).map f) = 0 ↔
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map f = 0 :=
  faithfullyFlatDerivedHomology_map_eq_zero_iff _ (powerResidueRingHom_faithfullyFlat a S hS k) n f

/-- The action of a fixed power of an original scalar descends with the same exponent. -/
lemma powerResidueDerivedHomology_scalar_eq_zero_iff (n : ℤ)
    (X : DerivedCategory (ModuleCat.{u} A)) (g : R) (N : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).map
        ((powerResidueDerivedBaseChange a S hS k).map
          ((Ideal.Quotient.mk (Ideal.span {a ^ k}) g) ^ N • 𝟙 X)) = 0 ↔
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        ((Ideal.Quotient.mk (Ideal.span {a ^ k}) g) ^ N • 𝟙 X) = 0 :=
  powerResidueDerivedHomology_map_eq_zero_iff a S hS k n _

/-- A common exponent is reflected for an entire family of stages and specified degrees.
This preserves the quantifier order: it does not produce a uniform exponent from stagewise ones. -/
lemma powerResidueDerivedHomology_uniform_scalar_eq_zero_iff
    (X : (j : ℕ) → DerivedCategory (ModuleCat.{u} (R ⧸ Ideal.span {a ^ j})))
    (g : R) (degrees : Set ℤ) :
    (∃ N : ℕ, ∀ j : ℕ, ∀ i ∈ degrees,
      (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (S ⧸ Ideal.map (algebraMap R S) (Ideal.span {a ^ j}))) i).map
          ((powerResidueDerivedBaseChange a S hS j).map
            ((Ideal.Quotient.mk (Ideal.span {a ^ j}) g) ^ N • 𝟙 (X j))) = 0) ↔
    (∃ N : ℕ, ∀ j : ℕ, ∀ i ∈ degrees,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ Ideal.span {a ^ j})) i).map
        ((Ideal.Quotient.mk (Ideal.span {a ^ j}) g) ^ N • 𝟙 (X j)) = 0) := by
  simp only [powerResidueDerivedHomology_scalar_eq_zero_iff]

end SerrePositivity
