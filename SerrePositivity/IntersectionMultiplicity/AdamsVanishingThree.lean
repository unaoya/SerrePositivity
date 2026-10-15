module

public import SerrePositivity.IntersectionMultiplicity.AdamsVanishing
public import SerrePositivity.IntersectionMultiplicity.CubicCyclotomicBaseChange
public import SerrePositivity.KTheory.Adams.CyclicThreeFamily
public import SerrePositivity.KTheory.Adams.CubicCoefficientField

/-! # Intersection vanishing in residue characteristic two via the cyclic Adams cube -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open Polynomial IsLocalRing TensorProduct
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Apply the cubic family on a chosen coprime-factor local model and preserve chi. -/
theorem intersectionVanishing_of_cubicCyclotomic_factor
    (g h : (ResidueField R)[X])
    (hf : cubicCyclotomicPolynomial (ResidueField R) = g * h)
    [Fact (Irreducible g)] (hc : IsCoprime g h)
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R)
    (htwo : (2 : ResidueField R) = 0) : chi R M N = 0 := by
  let B := CubicCyclotomicLocalRing g h hf
  let : Module R B := Algebra.toModule
  let : IsRegularLocalRing B := cubicCyclotomicLocalRing_regular g h hf hc
  let : Invertible (3 : B) := (cubicCyclotomicLocalRing_three_isUnit g h hf htwo).invertible
  obtain ⟨hM, hN, hfinB, hdimB, hchi⟩ :=
    cubicCyclotomicLocalRing_vanishing_data g h hf hc M N hfin hdim
  let : Module.Finite B (B ⊗[R] M) := hM
  let : Module.Finite B (B ⊗[R] N) := hN
  have hz := intersectionVanishing_of_adamsFamily
    (Adams.cyclicThreeFamily Adams.CubicCoefficientField (cubicCyclotomicLocalRoot g h hf)
      (cubicCyclotomicLocalRoot_relation g h hf)
      Adams.cubicCoefficientRoot Adams.cubicCoefficientRoot_relation)
    (B ⊗[R] M) (B ⊗[R] N) hfinB hdimB
  exact hchi.symm.trans hz

/-- The original hypotheses imply vanishing when residue 2 is zero. -/
theorem intersectionVanishing_of_residue_two_eq_zero
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R)
    (htwo : (2 : ResidueField R) = 0) : chi R M N = 0 := by
  obtain ⟨g, h, _, hi, hf, hc, _⟩ := exists_cubicCyclotomic_coprime_factor htwo
  let : Fact (Irreducible g) := ⟨hi⟩
  exact intersectionVanishing_of_cubicCyclotomic_factor g h hf hc M N hfin hdim htwo

end SerrePositivity
