import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedTensorQuotientComparison
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensor_outerQuotientUnit_isIso
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedCompletedTensorQuotientIso
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedCompletedTensorQuotientIso_outer_unit
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedCompletedTensorQuotientIso_units
assert_no_sorry SerrePositivity.DerivedCompletion.regularIteratedCompletedTensorQuotientIso

#print axioms SerrePositivity.DerivedCompletion.iteratedTensor_outerQuotientUnit_isIso
#print axioms SerrePositivity.DerivedCompletion.iteratedCompletedTensorQuotientIso
#print axioms SerrePositivity.DerivedCompletion.iteratedCompletedTensorQuotientIso_outer_unit
#print axioms SerrePositivity.DerivedCompletion.iteratedCompletedTensorQuotientIso_units
#print axioms SerrePositivity.DerivedCompletion.regularIteratedCompletedTensorQuotientIso

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable (R : Type u) [CommRing R] (p : ℕ) (d : R) (hd : IsSMulRegular R d)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

-- The original p,d completed tensor is covered; both factor inputs are supplied separately.
example (hS : IsSMulRegular S d) (hT : IsSMulRegular T d) :
    let q := Ideal.Quotient.mk (Ideal.span {d})
    let Q := R ⧸ Ideal.span {d}
    let SQ := S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
    let TQ := T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
    let AD := (boundedAboveCompletionCommMonFunctor R d).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    ((boundedAboveDerivedBaseChange q).obj AD.X).obj ≅
      (derivedComplexCompletionFunctor Q (q (p : R))).obj
        (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ).X.obj :=
  regularIteratedCompletedTensorQuotientIso R (p : R) d hd S T hS hT

-- A zero quotient base and zero factor quotients are admitted by the same theorem.
example (a : R) :
    let q := Ideal.Quotient.mk (Ideal.span {(1 : R)})
    let Q := R ⧸ Ideal.span {(1 : R)}
    let SQ := S ⧸ Ideal.map (algebraMap R S) (Ideal.span {(1 : R)})
    let TQ := T ⧸ Ideal.map (algebraMap R T) (Ideal.span {(1 : R)})
    let AD := (boundedAboveCompletionCommMonFunctor R 1).obj
      (boundedAboveCompletedTensorAlgebra R a S T)
    ((boundedAboveDerivedBaseChange q).obj AD.X).obj ≅
      (derivedComplexCompletionFunctor Q (q a)).obj
        (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ).X.obj :=
  regularIteratedCompletedTensorQuotientIso R a 1
    (by intro x y h; simpa only [one_smul] using h) S T
    (by intro x y h; simpa only [one_smul] using h)
    (by intro x y h; simpa only [one_smul] using h)
