import SerrePositivity.HomologicalAlgebra.DerivedTensorRealization
import Mathlib.Util.AssertNoSorry

-- G2-1: every explicit public declaration, including the maps and natural comparisons.
assert_no_sorry SerrePositivity.chainDerivedRealization
assert_no_sorry SerrePositivity.extendChainHomologyIso
assert_no_sorry SerrePositivity.extendHomotopyChainHomologyIso
assert_no_sorry SerrePositivity.chainDerivedRealizationHomologyIso
assert_no_sorry SerrePositivity.chainHomologyZeroProjection
assert_no_sorry SerrePositivity.chainHomologyZeroProjection_naturality
assert_no_sorry SerrePositivity.chainHomologyZeroProjection_homology
assert_no_sorry SerrePositivity.chainHomologyZeroProjectionNatTrans
assert_no_sorry SerrePositivity.homotopyChainHomologyZeroProjection
assert_no_sorry SerrePositivity.homotopyChainSingleHomologyIso
assert_no_sorry SerrePositivity.homotopyChainHomologyZeroProjection_homology
assert_no_sorry SerrePositivity.chainDerivedRealizationComplexNatIso
assert_no_sorry SerrePositivity.extendChainSingleNatIso
assert_no_sorry SerrePositivity.chainDerivedRealizationSingleNatIso
assert_no_sorry SerrePositivity.chainDerivedAugmentation
assert_no_sorry SerrePositivity.chainDerivedAugmentation_homology_diagram
assert_no_sorry SerrePositivity.realizedSingleH0Iso
assert_no_sorry SerrePositivity.chainDerivedAugmentation_homology
assert_no_sorry SerrePositivity.chainDerivedRealization_homology_isZero_positive
assert_no_sorry SerrePositivity.realizedDerivedTensorFunctor
assert_no_sorry SerrePositivity.realizedDerivedTensorMapLeft
assert_no_sorry SerrePositivity.realizedDerivedTensorMapLeft_id
assert_no_sorry SerrePositivity.realizedDerivedTensorMapLeft_comp
assert_no_sorry SerrePositivity.realizedDerivedTensorH0NatIso
assert_no_sorry SerrePositivity.realizedDerivedTensorAugmentation
assert_no_sorry SerrePositivity.realizedDerivedTensor
assert_no_sorry SerrePositivity.realizedDerivedTensorHomologyIso
assert_no_sorry SerrePositivity.realizedDerivedTensorH0Iso
assert_no_sorry SerrePositivity.realizedDerivedTensorAugmentation_homology
assert_no_sorry SerrePositivity.realizedDerivedTensor_discrete_iff

open CategoryTheory CategoryTheory.Limits SerrePositivity
noncomputable section
attribute [local instance] HasDerivedCategory.standard

-- Arbitrary coefficient rings and modules: no flatness, finite generation, or regularity.
example (R M N : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (realizedDerivedTensor R M N) ≅ ModuleCat.of R (TensorProduct R M N) :=
  realizedDerivedTensorH0Iso R M N

-- Negative cohomological degrees, including degree zero, agree with the old Tor model.
example (R M N : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat R) (-(n : ℤ))).obj
      (realizedDerivedTensor R M N) ≅
      ((Tor (ModuleCat R) n).obj (ModuleCat.of R M)).obj (ModuleCat.of R N) :=
  realizedDerivedTensorHomologyIso R M N n

-- The augmentation is a natural transformation with the actual derived-category target.
example (R : Type) [CommRing R] (M N N' : ModuleCat R) (f : N ⟶ N') :
    (realizedDerivedTensorFunctor R M).map f ≫
      (realizedDerivedTensorAugmentation R M).app N' =
    (realizedDerivedTensorAugmentation R M).app N ≫
      (((MonoidalCategory.tensoringLeft (ModuleCat R)).obj M) ⋙
        DerivedCategory.singleFunctor _ 0).map f :=
  (realizedDerivedTensorAugmentation R M).naturality f

#print axioms SerrePositivity.realizedDerivedTensorH0Iso
#print axioms SerrePositivity.realizedDerivedTensorAugmentation_homology
#print axioms SerrePositivity.realizedDerivedTensor_discrete_iff
