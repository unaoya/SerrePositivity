module

public import SerrePositivity.CommutativeAlgebra.CubicCyclotomicLocalExtension
public import SerrePositivity.IntersectionMultiplicity.BaseChange

/-! # Transporting the vanishing hypotheses to the cubic cyclotomic local extension -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open Polynomial IsLocalRing TensorProduct
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (g h : (ResidueField R)[X])
    (hf : cubicCyclotomicPolynomial (ResidueField R) = g * h)
    [Fact (Irreducible g)]

-- Use the R-action specified by the structural R-algebra, as in the preservation API.
local instance : Module R (CubicCyclotomicLocalRing g h hf) := Algebra.toModule

/-- All numerical hypotheses and the integer intersection value transfer to the same local model. -/
lemma cubicCyclotomicLocalRing_vanishing_data (hc : IsCoprime g h)
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R) :
    let B := CubicCyclotomicLocalRing g h hf
    Module.Finite B (B ⊗[R] M) ∧ Module.Finite B (B ⊗[R] N) ∧
      Module.length B ((B ⊗[R] M) ⊗[B] (B ⊗[R] N)) ≠ ⊤ ∧
      Module.supportDim B (B ⊗[R] M) + Module.supportDim B (B ⊗[R] N) < ringKrullDim B ∧
      chi B (B ⊗[R] M) (B ⊗[R] N) = chi R M N := by
  let B := CubicCyclotomicLocalRing g h hf
  have hm := cubicCyclotomicLocalRing_map_maximalIdeal g h hf hc
  refine ⟨inferInstance, inferInstance, ?_, ?_,
    chi_baseChange_of_map_maximalIdeal R B hm M N⟩
  · rw [tensorLength_baseChange_of_map_maximalIdeal R B hm M N]
    exact hfin
  · rw [supportDim_baseChange_of_map_maximalIdeal R B hm M,
      supportDim_baseChange_of_map_maximalIdeal R B hm N,
      cubicCyclotomicLocalRing_dimension g h hf hc]
    exact hdim

end SerrePositivity
