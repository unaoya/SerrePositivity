import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
import SerrePositivity.HomologicalAlgebra.FiniteCohomologyBaseChange
import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedAcyclic
import SerrePositivity.HomologicalAlgebra.BoundedAboveSourceConeTriangle
import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedConeTriangle
import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedShift
import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedCone
import SerrePositivity.HomologicalAlgebra.PowerResidueDerivedHomology
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorAnnihilator
import SerrePositivity.HomologicalAlgebra.TwoCohomologyAnnihilator
import SerrePositivity.HomologicalAlgebra.CompleteTwoCohomologyAnnihilator
import SerrePositivity.CommutativeAlgebra.CompletelyFlatPowerTorsion
import SerrePositivity.CommutativeAlgebra.CompletelyFaithfullyFlatPowers
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyLimOne_annihilated
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomologyLimit_annihilated
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimit_homology_annihilated
assert_no_sorry SerrePositivity.DerivedCompletion.complexTowerHomotopyLimit_homology_pow_annihilated
assert_no_sorry SerrePositivity.DerivedCompletion.homology_pow_annihilated_of_equiv_homotopyLimit
assert_no_sorry SerrePositivity.DerivedCompletion.derived_homology_pow_annihilated_of_iso_homotopyLimit

#print axioms SerrePositivity.DerivedCompletion.complexTowerHomotopyLimit_homology_pow_annihilated
#print axioms SerrePositivity.DerivedCompletion.derived_homology_pow_annihilated_of_iso_homotopyLimit

-- D5: abstract two-cohomology objects and actual module-map cones.
assert_no_sorry SerrePositivity.two_cohomology_scalar_product_eq_zero
assert_no_sorry SerrePositivity.two_cohomology_scalar_pow_eq_zero
assert_no_sorry SerrePositivity.two_cohomology_scalar_pow_eq_zero_of_iso_homotopyLimit
assert_no_sorry SerrePositivity.moduleMapConeScalar_pow_eq_zero_of_iso_homotopyLimit

open CategoryTheory SerrePositivity
attribute [local instance] HasDerivedCategory.standard

-- Only the cohomological bounds are inputs; a strict/projective representative is not.
example (R : Type) [CommRing R] (X : DerivedCategory (ModuleCat.{0} R))
    (a b : ℤ) (hab : a + 1 = b) [X.IsGE a] [X.IsLE b] (g : R) (N : ℕ)
    (ha : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{0} R) a).obj X, g ^ N • x = 0)
    (hb : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{0} R) b).obj X, g ^ N • x = 0) :
    g ^ (2 * N) • 𝟙 X = 0 := two_cohomology_scalar_pow_eq_zero R X a b hab g N ha hb

#print axioms SerrePositivity.two_cohomology_scalar_product_eq_zero
#print axioms SerrePositivity.moduleMapConeScalar_pow_eq_zero_of_iso_homotopyLimit

-- D4: the standard holim comparison is supplied by completeness, rather than an input iso.
assert_no_sorry SerrePositivity.DerivedCompletion.completeComplexKoszulHomologyEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.completeComplex_homology_pow_annihilated
assert_no_sorry SerrePositivity.DerivedCompletion.completeDerivedKoszulHomotopyLimitIso
assert_no_sorry SerrePositivity.DerivedCompletion.completeDerived_homology_pow_annihilated
assert_no_sorry SerrePositivity.complete_two_cohomology_scalar_pow_eq_zero
assert_no_sorry SerrePositivity.complete_moduleMapConeScalar_pow_eq_zero

-- General derived objects have no chosen strict or projective representative as input.
example (R : Type) [CommRing R] (p : R) (X : DerivedCompletion.ConcreteDerivedCategory R)
    (hX : DerivedCompletion.IsComplete R p X) (i : ℤ) (g : R) (N : ℕ)
    (h : ∀ n,
      (∀ x : (DerivedCompletion.complexPowerKoszulStage R p
        (DerivedCategory.Q.objPreimage X) n).homology i, g ^ N • x = 0) ∧
      (∀ x : (DerivedCompletion.complexPowerKoszulStage R p
        (DerivedCategory.Q.objPreimage X) n).homology (i - 1), g ^ N • x = 0))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X) : g ^ (2 * N) • x = 0 :=
  DerivedCompletion.completeDerived_homology_pow_annihilated R p X hX i g N h x

-- Scalar multiplication is transported by the actual R-linear standard comparison.
example (R : Type) [CommRing R] (p : R) (K : CochainComplex (ModuleCat R) ℤ)
    (hK : DerivedCompletion.IsComplete R p (DerivedCategory.Q.obj K)) (i : ℤ)
    (r : R) (x : K.homology i) :
    DerivedCompletion.completeComplexKoszulHomologyEquiv R p K hK i (r • x) =
      r • DerivedCompletion.completeComplexKoszulHomologyEquiv R p K hK i x :=
  (DerivedCompletion.completeComplexKoszulHomologyEquiv R p K hK i).map_smul r x

#print axioms SerrePositivity.DerivedCompletion.completeDerived_homology_pow_annihilated
#print axioms SerrePositivity.complete_moduleMapConeScalar_pow_eq_zero

-- D1: arbitrary rings and arbitrary torsion test modules, all exponents including zero.
assert_no_sorry SerrePositivity.torModule_subsingleton_of_completelyFlat_powerTorsion
assert_no_sorry SerrePositivity.isCompletelyFlat_principal_power
assert_no_sorry SerrePositivity.flat_residueTensor_of_completelyFlat
assert_no_sorry SerrePositivity.flat_power_residueTensor_of_completelyFlat
assert_no_sorry SerrePositivity.isCompletelyFlat_principal_ideal_pow
assert_no_sorry SerrePositivity.flat_algebraQuotient_of_completelyFlat
assert_no_sorry SerrePositivity.flat_power_algebraQuotient_of_completelyFlat

open scoped TensorProduct
attribute [local instance] adicQuotientAlgebra

-- No flatness of the original R-module, finiteness, or regularity of a is assumed.
example (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (hM : IsCompletelyFlat (Ideal.span {a}) M) (n : ℕ) :
    Module.Flat (R ⧸ Ideal.span {a ^ n}) ((R ⧸ Ideal.span {a ^ n}) ⊗[R] M) :=
  flat_power_residueTensor_of_completelyFlat a M hM n

-- Ring quotient actions use exactly the G1 interface's canonical residue algebra.
example (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (a : R) (hS : IsCompletelyFlat (Ideal.span {a}) S) (n : ℕ) :
    Module.Flat (R ⧸ Ideal.span {a ^ n})
      (S ⧸ (Ideal.span {a ^ n}).map (algebraMap R S)) :=
  flat_power_algebraQuotient_of_completelyFlat a S hS n

-- The zero-th stage is a quotient by a unit, without a nontriviality assumption.
example (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (hM : IsCompletelyFlat (Ideal.span {a}) M) :
    Module.Flat (R ⧸ Ideal.span {a ^ 0}) ((R ⧸ Ideal.span {a ^ 0}) ⊗[R] M) :=
  flat_power_residueTensor_of_completelyFlat a M hM 0

#print axioms SerrePositivity.torModule_subsingleton_of_completelyFlat_powerTorsion
#print axioms SerrePositivity.flat_residueTensor_of_completelyFlat
#print axioms SerrePositivity.flat_power_algebraQuotient_of_completelyFlat

-- D2: faithful power quotients, object detection, and original base-linear maps.
assert_no_sorry SerrePositivity.subsingleton_of_principal_power_torsion_of_reduction
assert_no_sorry SerrePositivity.subsingleton_of_power_torsion_of_residueTensor
assert_no_sorry SerrePositivity.faithfullyFlat_power_residueTensor_of_completelyFaithfullyFlat
assert_no_sorry SerrePositivity.power_residue_lTensor_eq_zero_iff
assert_no_sorry SerrePositivity.power_residue_lTensor_surjective_iff
assert_no_sorry SerrePositivity.faithfullyFlat_power_algebraQuotient_of_completelyFaithfullyFlat
assert_no_sorry SerrePositivity.principalPowerTorsionModule
assert_no_sorry SerrePositivity.principalPowerTorsionLinearMap
assert_no_sorry SerrePositivity.principalPowerTorsionLinearMap_apply
assert_no_sorry SerrePositivity.principalPowerTorsionLinearMap_eq_zero_iff
assert_no_sorry SerrePositivity.power_torsion_lTensor_eq_zero_iff
assert_no_sorry SerrePositivity.power_torsion_lTensor_surjective_iff

-- The original coefficient module has no ordinary R-faithfully-flat assumption.
example (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (hM : IsCompletelyFaithfullyFlat (Ideal.span {a}) M) (n : ℕ) :
    Module.FaithfullyFlat (R ⧸ Ideal.span {a ^ n}) ((R ⧸ Ideal.span {a ^ n}) ⊗[R] M) :=
  faithfullyFlat_power_residueTensor_of_completelyFaithfullyFlat a M hM n

-- The zero-th stage is the zero ring; it is included without a Nontrivial hypothesis.
example (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (hM : IsCompletelyFaithfullyFlat (Ideal.span {a}) M) :
    Module.FaithfullyFlat (R ⧸ Ideal.span {a ^ 0}) ((R ⧸ Ideal.span {a ^ 0}) ⊗[R] M) :=
  faithfullyFlat_power_residueTensor_of_completelyFaithfullyFlat a M hM 0

-- The map starts as an R-linear map, and the quotient actions are explicit local data.
example (R M N N' : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (a : R) (hM : IsCompletelyFaithfullyFlat (Ideal.span {a}) M) (n : ℕ)
    (hN : ∀ x : N, a ^ n • x = 0) (hN' : ∀ x : N', a ^ n • x = 0) (f : N →ₗ[R] N') :
    let _ := principalPowerTorsionModule a n N hN
    let _ := principalPowerTorsionModule a n N' hN'
    (principalPowerTorsionLinearMap a n hN hN' f).lTensor
      ((R ⧸ Ideal.span {a ^ n}) ⊗[R] M) = 0 ↔ f = 0 :=
  power_torsion_lTensor_eq_zero_iff a M hM n hN hN' f

#print axioms SerrePositivity.subsingleton_of_power_torsion_of_residueTensor
#print axioms SerrePositivity.faithfullyFlat_power_residueTensor_of_completelyFaithfullyFlat
#print axioms SerrePositivity.power_torsion_lTensor_surjective_iff

-- D3a: actual power residue rings, all homology maps and uniform scalar exponents.
assert_no_sorry SerrePositivity.faithfullyFlat_extendScalars_map_eq_zero_iff
assert_no_sorry SerrePositivity.flatDerivedBaseChange
assert_no_sorry SerrePositivity.boundedAboveFlatDerivedBaseChangeIso
assert_no_sorry SerrePositivity.flatDerivedBaseChangeHomologyNatIso
assert_no_sorry SerrePositivity.flatDerivedHomology_map_eq_zero_iff
assert_no_sorry SerrePositivity.faithfullyFlatDerivedHomology_map_eq_zero_iff
assert_no_sorry SerrePositivity.faithfullyFlatDerivedHomology_scalar_eq_zero_iff
assert_no_sorry SerrePositivity.powerResidueRingHom_faithfullyFlat
assert_no_sorry SerrePositivity.powerResidueDerivedBaseChange
assert_no_sorry SerrePositivity.powerResidueDerivedHomologyNatIso
assert_no_sorry SerrePositivity.powerResidueDerivedHomology_map_eq_zero_iff
assert_no_sorry SerrePositivity.powerResidueDerivedHomology_scalar_eq_zero_iff
assert_no_sorry SerrePositivity.powerResidueDerivedHomology_uniform_scalar_eq_zero_iff

#print axioms SerrePositivity.faithfullyFlatDerivedHomology_map_eq_zero_iff
#print axioms SerrePositivity.powerResidueDerivedHomology_uniform_scalar_eq_zero_iff

-- D3b: actual projective cone computations without exactness of the original functor.
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.cone
assert_no_sorry SerrePositivity.boundedAboveDerivedConeObject
assert_no_sorry SerrePositivity.boundedAboveDerivedConeInr
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedConeIso
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedConeIso_inr

#print axioms SerrePositivity.boundedAboveLeftDerivedConeIso_inr

-- D3b: shifted projective representatives and actual left-derived shift naturality.
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.transport
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.shift
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.shift_map_naturality
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.shiftMinus
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.shiftMinus_map_naturality
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedShiftIso
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedShiftIso_naturality
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedShiftNatIso

#print axioms SerrePositivity.boundedAboveLeftDerivedShiftNatIso

-- D3b: the third cone morphism, distinguished image triangle and homology exactness.
assert_no_sorry SerrePositivity.boundedAboveDerivedConeProjection
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedConeIso_projection_model
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedConeIso_projection
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedConeTriangle
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedConeTriangleIso
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedConeTriangle_distinguished
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedConeTriangle_homology_exact

#print axioms SerrePositivity.boundedAboveLeftDerivedConeTriangle_distinguished
#print axioms SerrePositivity.boundedAboveLeftDerivedConeTriangle_homology_exact

-- D3b: additive/linear derived maps and arbitrary bounded-above triangle images.
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.mapAddHomotopy
assert_no_sorry SerrePositivity.boundedAboveLeftDerived_additive
assert_no_sorry SerrePositivity.BoundedAboveDerivedModel.mapSmulHomotopy
assert_no_sorry SerrePositivity.boundedAboveLeftDerived_linear
assert_no_sorry SerrePositivity.boundedAboveSourceConeTriangle
assert_no_sorry SerrePositivity.boundedAboveSourceConeTriangleIso
assert_no_sorry SerrePositivity.boundedAboveSourceConeTriangle_distinguished
assert_no_sorry SerrePositivity.boundedAboveSourceConeTriangleIsoOfDistinguished
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedTriangle
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedTriangle_distinguished
assert_no_sorry SerrePositivity.boundedAboveLeftDerivedTriangle_homology_exact

#print axioms SerrePositivity.boundedAboveLeftDerived_linear
#print axioms SerrePositivity.boundedAboveLeftDerivedTriangle_distinguished
#print axioms SerrePositivity.boundedAboveLeftDerivedTriangle_homology_exact

-- D3b: upper bounds and the shifted Tor-acyclic base case.
assert_no_sorry SerrePositivity.boundedAboveLeftDerived_isLE
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangeAcyclicShiftIso
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangeAcyclicShiftIso_naturality
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChangeAcyclicShift_isGE

#print axioms SerrePositivity.boundedAboveLeftDerived_isLE
#print axioms SerrePositivity.boundedAboveDerivedBaseChangeAcyclicShiftIso_naturality
#print axioms SerrePositivity.boundedAboveDerivedBaseChangeAcyclicShift_isGE

-- D3b: actual cohomology Tor conditions and finite Postnikov lower-bound preservation.
assert_no_sorry SerrePositivity.scalarExtensionTorVanishing_of_iso
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChange_pure_isGE
assert_no_sorry SerrePositivity.derivedTruncLE_homology_isIso
assert_no_sorry SerrePositivity.derivedTruncGE_homology_isIso
assert_no_sorry SerrePositivity.homologyTorAcyclic
assert_no_sorry SerrePositivity.scalarExtensionTorVanishing_of_isZero
assert_no_sorry SerrePositivity.homologyTorAcyclic_truncLE
assert_no_sorry SerrePositivity.homologyTorAcyclic_truncGE
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChange_finite_isGE
assert_no_sorry SerrePositivity.boundedAboveDerivedBaseChange_isGE_of_homologyTorAcyclic

#print axioms SerrePositivity.boundedAboveDerivedBaseChange_finite_isGE
#print axioms SerrePositivity.boundedAboveDerivedBaseChange_isGE_of_homologyTorAcyclic

-- D3b: canonical pure layers, normalized by actual homology and natural in all maps.
assert_no_sorry SerrePositivity.exists_normalizedPureHomologyIso
assert_no_sorry SerrePositivity.normalizedPureHomologyIso
assert_no_sorry SerrePositivity.normalizedPureHomologyIso_homology
assert_no_sorry SerrePositivity.pureHomology_map_injective
assert_no_sorry SerrePositivity.normalizedPureHomologyIso_naturality
assert_no_sorry SerrePositivity.normalizedPureHomologyIso_unique

#print axioms SerrePositivity.normalizedPureHomologyIso_naturality
#print axioms SerrePositivity.normalizedPureHomologyIso_unique
