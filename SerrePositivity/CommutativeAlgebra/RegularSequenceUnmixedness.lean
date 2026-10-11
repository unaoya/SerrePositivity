module

public import SerrePositivity.CommutativeAlgebra.AssociatedPrimeDimension
public import SerrePositivity.CommutativeAlgebra.AssociatedPrimeDepth
public import SerrePositivity.CommutativeAlgebra.RegularQuotientDepth

/-! # Unmixedness of regular-sequence quotients of regular local rings

The associated-prime depth bound and the quotient depth lemma give the lower
dimension bound. The associated-prime injection into the quotient gives the
upper bound, using the dimension formula for a regular-sequence quotient.
-/

@[expose] public section

universe u

namespace SerrePositivity.RegularSequenceUnmixedness

open IsLocalRing

/-- Every associated prime of a regular-sequence quotient has the expected dimension.
The associated-prime hypothesis rules out the zero quotient, even when the input
sequence is only weakly regular. -/
theorem dimension_eq {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (rs : List R) (hrs : RingTheory.Sequence.IsWeaklyRegular R rs)
    {p : Ideal R} (hp : p ∈ associatedPrimes R (R ⧸ Ideal.ofList rs)) :
    ringKrullDim (R ⧸ p) + rs.length = ringKrullDim R := by
  have hreg := AssociatedPrimeDimension.isRegular_of_isWeaklyRegular_of_mem_associatedPrimes
    rs hrs hp
  have hupper := AssociatedPrimeDimension.ringKrullDim_quotient_le_supportDim hp
  rw [Module.supportDim_quotient_eq_ringKrullDim] at hupper
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hreg
  apply le_antisymm ((add_le_add hupper le_rfl).trans_eq hdim)
  have hdepth := RegularQuotientDepth.dimToNat_le_depth_ringQuotient_add_length R rs hrs
  have hdepth' : (dimToNat (ringKrullDim R) : WithBot ℕ∞) ≤
      (IsLocalRing.depth (ModuleCat.of R (R ⧸ Ideal.ofList rs)) : WithBot ℕ∞) + rs.length := by
    exact_mod_cast hdepth
  rw [PrimaryParameterExistence.natCast_dimToNat R] at hdepth'
  exact hdepth'.trans (add_le_add
    (depth_le_dim_quotient_of_mem_associatedPrimes (ModuleCat.of R (R ⧸ Ideal.ofList rs)) hp)
    le_rfl)

end SerrePositivity.RegularSequenceUnmixedness
