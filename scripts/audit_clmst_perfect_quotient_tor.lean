import SerrePositivity.HomologicalAlgebra.PerfectRadicalQuotientTor
import SerrePositivity.CommutativeAlgebra.CompatibleRootFamilyIdeal
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.compatibleRootIdeal
assert_no_sorry SerrePositivity.span_root_zero_le_compatibleRootIdeal
assert_no_sorry SerrePositivity.compatibleRoot_principal_monotone
assert_no_sorry SerrePositivity.mem_compatibleRootIdeal_iff
assert_no_sorry SerrePositivity.compatibleRootIdeal_mul_self
assert_no_sorry SerrePositivity.compatibleRootIdeal_le_ker_of_root_zero
assert_no_sorry SerrePositivity.compatibleRootIdeal_map
assert_no_sorry SerrePositivity.compatibleRoot_annihilator_le_succ
assert_no_sorry SerrePositivity.compatibleRoot_transition_kills_kernel
assert_no_sorry SerrePositivity.compatibleRootIdeal_flat
assert_no_sorry SerrePositivity.compatibleRootIdealElement
assert_no_sorry SerrePositivity.compatibleRootIdeal_tensor_singleStage
assert_no_sorry SerrePositivity.compatibleRootIdealTensorMap
assert_no_sorry SerrePositivity.compatibleRootIdealTensorMap_injective
assert_no_sorry SerrePositivity.compatibleRootQuotient_tor_subsingleton
assert_no_sorry SerrePositivity.compatibleRootQuotient_derivedTensor_concentrated
assert_no_sorry SerrePositivity.compatibleRootIdeal_map_frobenius_eq
assert_no_sorry SerrePositivity.compatibleRootQuotient_perfectRing
assert_no_sorry SerrePositivity.compatibleRootFamilyZeroIdeal
assert_no_sorry SerrePositivity.compatibleRootFamilyIdeal
assert_no_sorry SerrePositivity.compatibleRootFamilyIdeal_eq_iSup
assert_no_sorry SerrePositivity.compatibleRootFamilyZeroIdeal_le
assert_no_sorry SerrePositivity.compatibleRootFamilyIdeal_le_ker
assert_no_sorry SerrePositivity.compatibleRootFamilyIdeal_mul_self
assert_no_sorry SerrePositivity.compatibleRootFamilyIdeal_map_frobenius_eq
assert_no_sorry SerrePositivity.compatibleRootFamilyQuotient_perfectRing
assert_no_sorry SerrePositivity.coefficientTensorLift
assert_no_sorry SerrePositivity.coefficientTensorLift_tmul
assert_no_sorry SerrePositivity.perfectCoefficientTensorRoot
assert_no_sorry SerrePositivity.perfectCoefficientTensorRoot_tmul
assert_no_sorry SerrePositivity.perfectCoefficientTensor_perfectRing
assert_no_sorry SerrePositivity.isReduced_of_perfectPower
assert_no_sorry SerrePositivity.doubleQuotientModuleIso
assert_no_sorry SerrePositivity.quotientSupTorAcyclicBaseChangeIso
assert_no_sorry SerrePositivity.compatibleRootFiniteFamilyQuotient_tor_subsingleton
assert_no_sorry SerrePositivity.finiteSupQuotientDiagram
assert_no_sorry SerrePositivity.finiteSupQuotientCocone
assert_no_sorry SerrePositivity.finiteSupQuotient_isColimit
assert_no_sorry SerrePositivity.finiteSupQuotientColimitIso
assert_no_sorry SerrePositivity.finiteSupQuotientColimitIso_ι
assert_no_sorry SerrePositivity.compatibleRootSupQuotient_tor_subsingleton
assert_no_sorry SerrePositivity.compatibleRootFamilyQuotient_tor_subsingleton
assert_no_sorry SerrePositivity.perfectRadicalIdealRootFamily
assert_no_sorry SerrePositivity.perfectRadicalIdealRootFamily_pow
assert_no_sorry SerrePositivity.perfectRadicalIdealRootFamily_ideal_eq
assert_no_sorry SerrePositivity.radicalIdeal_quotient_tor_subsingleton_of_perfectRing
assert_no_sorry SerrePositivity.perfectRing_surjective_tor_subsingleton
assert_no_sorry SerrePositivity.baseChangeScalarAlgebraEquiv
#print axioms SerrePositivity.compatibleRootIdeal
#print axioms SerrePositivity.span_root_zero_le_compatibleRootIdeal
#print axioms SerrePositivity.compatibleRoot_principal_monotone
#print axioms SerrePositivity.mem_compatibleRootIdeal_iff
#print axioms SerrePositivity.compatibleRootIdeal_mul_self
#print axioms SerrePositivity.compatibleRootIdeal_le_ker_of_root_zero
#print axioms SerrePositivity.compatibleRootIdeal_map
#print axioms SerrePositivity.compatibleRoot_annihilator_le_succ
#print axioms SerrePositivity.compatibleRoot_transition_kills_kernel
#print axioms SerrePositivity.compatibleRootIdeal_flat
#print axioms SerrePositivity.compatibleRootIdealElement
#print axioms SerrePositivity.compatibleRootIdeal_tensor_singleStage
#print axioms SerrePositivity.compatibleRootIdealTensorMap
#print axioms SerrePositivity.compatibleRootIdealTensorMap_injective
#print axioms SerrePositivity.compatibleRootQuotient_tor_subsingleton
#print axioms SerrePositivity.compatibleRootQuotient_derivedTensor_concentrated
#print axioms SerrePositivity.compatibleRootIdeal_map_frobenius_eq
#print axioms SerrePositivity.compatibleRootQuotient_perfectRing
#print axioms SerrePositivity.compatibleRootFamilyZeroIdeal
#print axioms SerrePositivity.compatibleRootFamilyIdeal
#print axioms SerrePositivity.compatibleRootFamilyIdeal_eq_iSup
#print axioms SerrePositivity.compatibleRootFamilyZeroIdeal_le
#print axioms SerrePositivity.compatibleRootFamilyIdeal_le_ker
#print axioms SerrePositivity.compatibleRootFamilyIdeal_mul_self
#print axioms SerrePositivity.compatibleRootFamilyIdeal_map_frobenius_eq
#print axioms SerrePositivity.compatibleRootFamilyQuotient_perfectRing
#print axioms SerrePositivity.coefficientTensorLift
#print axioms SerrePositivity.coefficientTensorLift_tmul
#print axioms SerrePositivity.perfectCoefficientTensorRoot
#print axioms SerrePositivity.perfectCoefficientTensorRoot_tmul
#print axioms SerrePositivity.perfectCoefficientTensor_perfectRing
#print axioms SerrePositivity.isReduced_of_perfectPower
#print axioms SerrePositivity.doubleQuotientModuleIso
#print axioms SerrePositivity.quotientSupTorAcyclicBaseChangeIso
#print axioms SerrePositivity.compatibleRootFiniteFamilyQuotient_tor_subsingleton
#print axioms SerrePositivity.finiteSupQuotientDiagram
#print axioms SerrePositivity.finiteSupQuotientCocone
#print axioms SerrePositivity.finiteSupQuotient_isColimit
#print axioms SerrePositivity.finiteSupQuotientColimitIso
#print axioms SerrePositivity.finiteSupQuotientColimitIso_ι
#print axioms SerrePositivity.compatibleRootSupQuotient_tor_subsingleton
#print axioms SerrePositivity.compatibleRootFamilyQuotient_tor_subsingleton
#print axioms SerrePositivity.perfectRadicalIdealRootFamily
#print axioms SerrePositivity.perfectRadicalIdealRootFamily_pow
#print axioms SerrePositivity.perfectRadicalIdealRootFamily_ideal_eq
#print axioms SerrePositivity.radicalIdeal_quotient_tor_subsingleton_of_perfectRing
#print axioms SerrePositivity.perfectRing_surjective_tor_subsingleton
#print axioms SerrePositivity.baseChangeScalarAlgebraEquiv

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] [PerfectRing R p]

-- Arbitrary radical ideals, arbitrary perfect coefficients, all positive degrees.
example (I : Ideal R) (hI : I.IsRadical) (C : Type u) [CommRing C]
    [Algebra R C] [PerfectRing C p] (i : ℕ) (hi : 0 < i) :
    Subsingleton (TorModule R i (R ⧸ I) C) :=
  radicalIdeal_quotient_tor_subsingleton_of_perfectRing I hI C i hi

-- No characteristic or nontriviality condition is added to the surjective target.
example (S : Type u) [CommRing S] [Algebra R S] [PerfectRing S p]
    (hs : Function.Surjective (algebraMap R S))
    (C : Type u) [CommRing C] [Algebra R C] [PerfectRing C p]
    (i : ℕ) (hi : 0 < i) : Subsingleton (TorModule R i S C) :=
  perfectRing_surjective_tor_subsingleton S hs C i hi

-- A zero quotient is retained in the radical-ideal statement.
example (C : Type u) [CommRing C] [Algebra R C] [PerfectRing C p]
    (i : ℕ) (hi : 0 < i) : Subsingleton (TorModule R i (R ⧸ (⊤ : Ideal R)) C) :=
  radicalIdeal_quotient_tor_subsingleton_of_perfectRing ⊤ (by intro x hx; trivial) C i hi

-- Empty index families use the same actual quotient diagram and canonical maps.
example (I : PEmpty → Ideal R) (s : Finset PEmpty) :
    colimit.ι (finiteSupQuotientDiagram I) s ≫ (finiteSupQuotientColimitIso I).hom =
      (finiteSupQuotientCocone I).ι.app s :=
  finiteSupQuotientColimitIso_ι I s

-- The finite family comparison has no regularity premise on any root.
example {σ : Type u} (s : Finset σ) (κ : σ → ℕ → R)
    (hκ : ∀ a n, κ a (n + 1) ^ p = κ a n)
    (C : Type u) [CommRing C] [Algebra R C] [PerfectRing C p]
    (i : ℕ) (hi : 0 < i) :
    Subsingleton (TorModule R i (R ⧸ s.sup (fun a => compatibleRootIdeal (κ a))) C) :=
  compatibleRootFiniteFamilyQuotient_tor_subsingleton s R κ hκ C i hi
