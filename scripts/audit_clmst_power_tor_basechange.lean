import SerrePositivity.HomologicalAlgebra.PowerTorsionTorBaseChange
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.torAlgebraAcyclicBaseChangeIso
assert_no_sorry SerrePositivity.torCoefficientScalarEndomorphism_acyclicBaseChange_eq_zero_iff
assert_no_sorry SerrePositivity.scalarExtensionTorVanishing_of_flat_algebra
assert_no_sorry SerrePositivity.scalarExtension_annihilated
assert_no_sorry SerrePositivity.powerTorsionTorInput_of_flat_baseChange
#print axioms SerrePositivity.torAlgebraAcyclicBaseChangeIso
#print axioms SerrePositivity.torCoefficientScalarEndomorphism_acyclicBaseChange_eq_zero_iff
#print axioms SerrePositivity.scalarExtensionTorVanishing_of_flat_algebra
#print axioms SerrePositivity.scalarExtension_annihilated
#print axioms SerrePositivity.powerTorsionTorInput_of_flat_baseChange

noncomputable section
universe u
open CategoryTheory SerrePositivity
variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]

-- The coefficient comparison is an actual C-linear isomorphism, all degrees.
example (M : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing (algebraMap R B) M) (i : ℕ) :
    ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M ≅
      ((ModuleCat.extendScalars (algebraMap B C)).leftDerived i).obj
        ((ModuleCat.extendScalars (algebraMap R B)).obj M) :=
  torAlgebraAcyclicBaseChangeIso M hM i

-- The original zero-action statement is compared, for every coefficient scalar.
example (M : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing (algebraMap R B) M) (i : ℕ) (c : C) :
    torCoefficientScalarEndomorphism C M i c = 0 ↔
      torCoefficientScalarEndomorphism C
        ((ModuleCat.extendScalars (algebraMap R B)).obj M) i c = 0 :=
  torCoefficientScalarEndomorphism_acyclicBaseChange_eq_zero_iff M hM i c

-- Arbitrary R tests stay arbitrary; no finite-generation or completeness premise.
example [Module.Flat R B] (p : ℕ) (I : Ideal B)
    (hTor : ∀ (L : ModuleCat.{u} B) (k : ℕ), 0 < k →
      (∀ x : L, (p : B) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ b ∈ I, torCoefficientScalarEndomorphism C L j (algebraMap B C b) = 0)
    (N : ModuleCat.{u} R) (k : ℕ) (hk : 0 < k)
    (hN : ∀ x : N, (p : R) ^ k • x = 0)
    (j : ℕ) (hj : 0 < j) (b : B) (hb : b ∈ I) :
    torCoefficientScalarEndomorphism C N j (algebraMap B C b) = 0 :=
  powerTorsionTorInput_of_flat_baseChange p I hTor N k hk hN j hj b hb
