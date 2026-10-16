module

public import SerrePositivity.HomologicalAlgebra.PerfectResidueTensorRegular
public import SerrePositivity.BhattScholze.PerfectDeltaCompletedTensorDiscrete

/-! # The ordinary tensor of perfect delta rings is p-torsion-free

This supplies the regularity input for constructing a tensor Frobenius lift.
A perfect delta structure on the tensor is not constructed here.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- No flatness or completeness assumption is required on the original algebra diagram. -/
lemma perfectDelta_tensor_p_mul_injective
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect) :
    Function.Injective (fun x : S ⊗[R] T => (p : S ⊗[R] T) * x) := by
  have := hR.perfectRing_mod_p
  have := perfectDeltaAlgebra_perfectRing_residue p R S DS hS
  have := perfectDeltaAlgebra_perfectRing_residue p R T DT hT
  exact tensor_p_mul_injective_of_perfect_residue p R S T hR.p_mul_injective
    (perfectDeltaAlgebra_p_regular p R S DS hS) (perfectDeltaAlgebra_p_regular p R T DT hT)

end SerrePositivity.BhattScholze
