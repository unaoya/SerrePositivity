module

public import SerrePositivity.IntersectionMultiplicity.AdamsVanishing
public import SerrePositivity.KTheory.Adams.CyclicTwoFamily
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Intersection vanishing away from residue characteristic two -/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open IsLocalRing TensorProduct
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A residue-field nonzero 2 supplies the inverse needed by the cyclic Adams square. -/
lemma isUnit_two_of_residue_ne_zero (h : (2 : ResidueField R) ≠ 0) : IsUnit (2 : R) := by
  apply (residue_ne_zero_iff_isUnit (2 : R)).mp
  simpa only [map_ofNat] using h

/-- The original hypotheses imply vanishing when residue 2 is nonzero. -/
theorem intersectionVanishing_of_residue_two_ne_zero
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R)
    (htwo : (2 : ResidueField R) ≠ 0) : chi R M N = 0 := by
  let : Invertible (2 : R) := (isUnit_two_of_residue_ne_zero htwo).invertible
  exact intersectionVanishing_of_adamsFamily (Adams.cyclicTwoFamily ℚ) M N hfin hdim

end SerrePositivity
