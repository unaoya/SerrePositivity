module

public import SerrePositivity.CommutativeAlgebra.CompletelyFaithfullyFlatPowers
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Completely faithfully flat algebra maps are injective on a separated base

Faithful flatness of every ordinary power quotient detects each original scalar.
The source needs only adic separatedness, and the target need not be complete.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
attribute [local instance] adicQuotientAlgebra

/-- A completely faithfully flat map is injective when its original base is adically separated. -/
theorem algebraMap_injective_of_completelyFaithfullyFlat_of_isHausdorff
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (a : R) [IsHausdorff (Ideal.span {a}) R]
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) S) :
    Function.Injective (algebraMap R S) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  change algebraMap R S x = 0 at hx
  apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) R) x
  intro n
  let I := Ideal.span {a ^ n}
  let : Module.FaithfullyFlat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    faithfullyFlat_power_algebraQuotient_of_completelyFaithfullyFlat a S hS n
  have hi : Function.Injective (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))) :=
    FaithfulSMul.algebraMap_injective _ _
  have hm : Ideal.Quotient.mk I x = 0 := by
    apply hi
    rw [map_zero]
    change Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S x) = 0
    rw [hx, map_zero]
  apply SModEq.zero.mpr
  change x ∈ (Ideal.span {a}) ^ n • (⊤ : Ideal R)
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hm

end SerrePositivity
