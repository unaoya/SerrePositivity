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
