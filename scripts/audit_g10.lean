import SerrePositivity.HomologicalAlgebra.DerivedFlatModelTensor
import SerrePositivity.CommutativeAlgebra.CompletelyFlatNilpotent
import Mathlib.Util.AssertNoSorry

universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity

assert_no_sorry SerrePositivity.moduleProperty_of_idealPower_annihilated
#print axioms SerrePositivity.moduleProperty_of_idealPower_annihilated
assert_no_sorry SerrePositivity.moduleProperty_of_nilpotentIdeal
#print axioms SerrePositivity.moduleProperty_of_nilpotentIdeal
assert_no_sorry SerrePositivity.torModule_subsingleton_of_completelyFlat_idealPowerTorsion
#print axioms SerrePositivity.torModule_subsingleton_of_completelyFlat_idealPowerTorsion
assert_no_sorry SerrePositivity.flat_of_completelyFlat_nilpotent
#print axioms SerrePositivity.flat_of_completelyFlat_nilpotent
assert_no_sorry SerrePositivity.isCompletelyFlat_nilpotent_iff_flat
#print axioms SerrePositivity.isCompletelyFlat_nilpotent_iff_flat
assert_no_sorry SerrePositivity.flat_of_acyclic_flat_nilpotent_reduction
#print axioms SerrePositivity.flat_of_acyclic_flat_nilpotent_reduction

-- G10 input: arbitrary nilpotent ideal, with no regularity or finite generation.
example {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : ∃ n : ℕ, I ^ n = ⊥) (hM : IsCompletelyFlat I M) :
    Module.Flat R M := flat_of_completelyFlat_nilpotent I hI M hM

-- Include nilpotence exponent zero whenever the coefficient ring allows it.
example {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I ^ 0 = ⊥) (hM : IsCompletelyFlat I M) : Module.Flat R M :=
  flat_of_completelyFlat_nilpotent I ⟨0, hI⟩ M hM

-- Only the already discrete case is claimed at this preparatory stage.
example {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : ∃ n : ℕ, I ^ n = ⊥)
    (hTor : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R M))
    (hFlat : Module.Flat (R ⧸ I)
      ((ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).obj (ModuleCat.of R M))) :
    Module.Flat R M := flat_of_acyclic_flat_nilpotent_reduction I hI M hTor hFlat

-- Actual bounded-above models, flat tensor exactness, and nilpotent coefficient tests.
assert_no_sorry SerrePositivity.moduleTensorCochainFunctor
#print axioms SerrePositivity.moduleTensorCochainFunctor
assert_no_sorry SerrePositivity.moduleTensorCochainFunctor_additive
#print axioms SerrePositivity.moduleTensorCochainFunctor_additive
assert_no_sorry SerrePositivity.moduleTensorCochain_shortExact
#print axioms SerrePositivity.moduleTensorCochain_shortExact
assert_no_sorry SerrePositivity.moduleTensorCochain_homology_isZero_extension
#print axioms SerrePositivity.moduleTensorCochain_homology_isZero_extension
assert_no_sorry SerrePositivity.moduleTensorCochain_homology_isZero_of_nilpotentIdeal
#print axioms SerrePositivity.moduleTensorCochain_homology_isZero_of_nilpotentIdeal
assert_no_sorry SerrePositivity.moduleTensorCochainUnitIso
#print axioms SerrePositivity.moduleTensorCochainUnitIso
assert_no_sorry SerrePositivity.cochain_homology_isZero_of_nilpotentIdeal_tests
#print axioms SerrePositivity.cochain_homology_isZero_of_nilpotentIdeal_tests
assert_no_sorry SerrePositivity.derivedTensorUnresolvedModuleModelIso
#print axioms SerrePositivity.derivedTensorUnresolvedModuleModelIso
assert_no_sorry SerrePositivity.derivedTensorModule_homology_isZero_of_flat_right
#print axioms SerrePositivity.derivedTensorModule_homology_isZero_of_flat_right
assert_no_sorry SerrePositivity.moduleTensorCochain_model_homology_isZero_of_pure_flat
#print axioms SerrePositivity.moduleTensorCochain_model_homology_isZero_of_pure_flat

-- Arbitrary upper bound of X: it is not assumed to be discrete before taking the model.
attribute [local instance] HasDerivedCategory.standard in
example {R : Type u} [CommRing R]
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (P : BoundedAboveDerivedModel X.obj)
    (hPure : ∀ j : ℤ, j ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj X.obj))
    (hFlat : Module.Flat R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj))
    (M : ModuleCat.{u} R) (i : ℤ) (hi : i ≠ 0) :
    IsZero (((moduleTensorCochainFunctor P.complex).obj M).homology i) :=
  moduleTensorCochain_model_homology_isZero_of_pure_flat X P hPure hFlat M i hi
