module

public import SerrePositivity.IntersectionMultiplicity.AdamsVanishingTwo
public import SerrePositivity.IntersectionMultiplicity.AdamsVanishingThree

/-! # Intersection vanishing in all residue characteristics by supported Adams operations -/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open IsLocalRing TensorProduct
variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- The Roberts–Gillet–Soulé vanishing theorem proved using the cyclic Adams square and cube. -/
theorem intersectionVanishing_of_adams
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R) :
    chi R M N = 0 := by
  by_cases htwo : (2 : ResidueField R) = 0
  · exact intersectionVanishing_of_residue_two_eq_zero M N hfin hdim htwo
  · exact intersectionVanishing_of_residue_two_ne_zero M N hfin hdim htwo

end SerrePositivity
