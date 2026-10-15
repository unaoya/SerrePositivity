import SerrePositivity.PerfectComplex.IntegerEulerIso
import SerrePositivity.KTheory.Adams.MaximalPureWeight
import SerrePositivity.CommutativeAlgebra.RegularLocalization
import SerrePositivity.IntersectionMultiplicity.EqualCharZeroPositivity
import Mathlib.Util.AssertNoSorry

open SerrePositivity
universe u
example (R : Type u) [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R = 0) :
    ∃ z : Fin 0 → R, Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R ∧
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn z) := by
  obtain ⟨n, z, hz, hreg, hn⟩ := exists_regular_generators_fin R
  have hn0 : n = 0 := by exact_mod_cast hn.symm.trans h
  subst n
  exact ⟨z, hz, hreg⟩

assert_no_sorry SerrePositivity.exists_regular_generators_fin
assert_no_sorry SerrePositivity.K0WithSupport.exists_integerEulerEquiv
assert_no_sorry SerrePositivity.Adams.SupportedAdams.maximal_pureWeight
assert_no_sorry SerrePositivity.exists_localized_height_koszulResolution
assert_no_sorry SerrePositivity.exists_mvPowerSeries_ringEquiv_of_charZero
#print axioms SerrePositivity.exists_regular_generators_fin
#print axioms SerrePositivity.exists_mvPowerSeries_ringEquiv_of_charZero
