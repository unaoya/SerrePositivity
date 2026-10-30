module

public import SerrePositivity.KTheory.G0Supported
public import SerrePositivity.CommutativeAlgebra.Length.Basic

/-! # Integer length on the Grothendieck group supported at a closed point -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits IsLocalRing
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A finite module supported at the maximal ideal has finite length. -/
lemma maximalSupportedModule_finiteLength
    (M : SupportedFGModuleOn (supportZeroLocus (maximalIdeal R))) : IsFiniteLength R M.obj := by
  have := M.property.1
  have hs := M.property.2
  change Module.support R M.obj ⊆ PrimeSpectrum.zeroLocus (maximalIdeal R) at hs
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hs
  let := Ideal.Quotient.field (maximalIdeal R)
  exact isFiniteLength_of_le_radical_annihilator (maximalIdeal R) M.obj hs

/-- Length, as a group homomorphism on modules supported at the maximal ideal. -/
def maximalSupportLengthMap : G0WithSupport (supportZeroLocus (maximalIdeal R)) →+ ℤ :=
  G0WithSupport.lift (fun M => ((Module.length R M.obj).toNat : ℤ))
    (fun e => congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) e.toLinearEquiv.length_eq)
    (fun E => by
      exact_mod_cast lengthNat_add_of_exact E.f E.g E.injective E.surjective E.exact
        (maximalSupportedModule_finiteLength R E.middle))

@[simp] lemma maximalSupportLengthMap_mk
    (M : SupportedFGModuleOn (supportZeroLocus (maximalIdeal R))) :
    maximalSupportLengthMap R (G0WithSupport.mk M) = ((Module.length R M.obj).toNat : ℤ) := by
  simp [maximalSupportLengthMap]

end SerrePositivity
