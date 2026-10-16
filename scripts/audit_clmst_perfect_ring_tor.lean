import SerrePositivity.HomologicalAlgebra.PerfectRingTor
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.perfectRing_tor_subsingleton
assert_no_sorry SerrePositivity.perfectRing_tor_subsingleton_of_char_eq_zero
assert_no_sorry SerrePositivity.perfectRing_derivedTensor_concentrated
assert_no_sorry SerrePositivity.perfectRing_derivedTensorAlgebraAugmentation_isIso
assert_no_sorry SerrePositivity.perfectRing_derivedTensor_concentrated_of_char_eq_zero
assert_no_sorry SerrePositivity.perfectRing_derivedTensorAlgebraAugmentation_isIso_of_char_eq_zero

#print axioms SerrePositivity.perfectRing_tor_subsingleton
#print axioms SerrePositivity.perfectRing_tor_subsingleton_of_char_eq_zero
#print axioms SerrePositivity.perfectRing_derivedTensor_concentrated
#print axioms SerrePositivity.perfectRing_derivedTensorAlgebraAugmentation_isIso
#print axioms SerrePositivity.perfectRing_derivedTensor_concentrated_of_char_eq_zero
#print axioms SerrePositivity.perfectRing_derivedTensorAlgebraAugmentation_isIso_of_char_eq_zero

noncomputable section
universe u
open CategoryTheory SerrePositivity
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [PerfectRing R p]
    (S C : Type u) [CommRing S] [CommRing C] [Algebra R S] [Algebra R C]
    [PerfectRing S p] [PerfectRing C p]

-- No surjectivity, flatness, finiteness or nontriviality assumptions on the algebras.
example [CharP R p] (i : ℕ) (hi : 0 < i) : Subsingleton (TorModule R i S C) :=
  perfectRing_tor_subsingleton (p := p) S C i hi

-- The base can also be the zero ring; a CharP instance is not requested.
example (hp : (p : R) = 0) (i : ℕ) (hi : 0 < i) : Subsingleton (TorModule R i S C) :=
  perfectRing_tor_subsingleton_of_char_eq_zero p R hp S C i hi

example [Subsingleton R] (i : ℕ) (hi : 0 < i) : Subsingleton (TorModule R i S C) :=
  perfectRing_tor_subsingleton_of_char_eq_zero p R (Subsingleton.elim _ _) S C i hi

example (hp : (p : R) = 0) : IsConcentratedInDegreeZero (derivedTensor R S C) :=
  perfectRing_derivedTensor_concentrated_of_char_eq_zero p R hp S C

example (hp : (p : R) = 0) :
    IsIso (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S C).hom.hom :=
  perfectRing_derivedTensorAlgebraAugmentation_isIso_of_char_eq_zero p R hp S C

-- A zero target is included without a CharP instance on it.
example [CharP R p] (i : ℕ) (hi : 0 < i) :
    Subsingleton (TorModule R i (R ⧸ (⊤ : Ideal R)) C) := by
  have : PerfectRing (R ⧸ (⊤ : Ideal R)) p :=
    { bijective_frobenius := ⟨fun _ _ _ => Subsingleton.elim _ _,
        fun x => ⟨0, Subsingleton.elim _ x⟩⟩ }
  exact perfectRing_tor_subsingleton (p := p) _ C i hi
