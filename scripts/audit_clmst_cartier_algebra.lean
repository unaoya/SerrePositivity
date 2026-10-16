import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedTensorCartierAlgebra
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.mappedPrincipalQuotientAlgEquiv
assert_no_sorry SerrePositivity.mappedPrincipalQuotientAlgEquiv_mk
assert_no_sorry SerrePositivity.mappedPrincipalQuotientAlgEquiv_symm_mk
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensorH0LeftAlgHom
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensorCartierLeftAlgHom
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensorCartierLeftAlgHom_mk
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensorH0RightAlgHom
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensorCartierRightAlgHom
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensorCartierRightAlgHom_mk
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensorCartierTensorAlgHom
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensorCartierTensorAlgHom_tmul
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensorCartierCompletedAlgHom
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensorCartierCompletedAlgHom_unit

#print axioms SerrePositivity.mappedPrincipalQuotientAlgEquiv
#print axioms SerrePositivity.mappedPrincipalQuotientAlgEquiv_mk
#print axioms SerrePositivity.mappedPrincipalQuotientAlgEquiv_symm_mk
#print axioms SerrePositivity.DerivedCompletion.iteratedTensorH0LeftAlgHom
#print axioms SerrePositivity.DerivedCompletion.iteratedTensorCartierLeftAlgHom
#print axioms SerrePositivity.DerivedCompletion.iteratedTensorCartierLeftAlgHom_mk
#print axioms SerrePositivity.DerivedCompletion.iteratedTensorH0RightAlgHom
#print axioms SerrePositivity.DerivedCompletion.iteratedTensorCartierRightAlgHom
#print axioms SerrePositivity.DerivedCompletion.iteratedTensorCartierRightAlgHom_mk
#print axioms SerrePositivity.DerivedCompletion.iteratedTensorCartierTensorAlgHom
#print axioms SerrePositivity.DerivedCompletion.iteratedTensorCartierTensorAlgHom_tmul
#print axioms SerrePositivity.DerivedCompletion.iteratedTensorCartierCompletedAlgHom
#print axioms SerrePositivity.DerivedCompletion.iteratedTensorCartierCompletedAlgHom_unit

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (a d : R) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "AP" => boundedAboveCompletedTensorAlgebra R a S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})

-- The original ordinary residue tensor has its original product of factor images.
example (s : S) (t : T) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    iteratedTensorCartierTensorAlgHom R a d S T
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) s ⊗ₜ[Q]
          Ideal.Quotient.mk (Ideal.map (algebraMap R T) (Ideal.span {d})) t) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d}) (iteratedTensorH0LeftAlgHom R a d S T s) *
        Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
          (iteratedTensorH0RightAlgHom R a d S T t) :=
  iteratedTensorCartierTensorAlgHom_tmul R a d S T s t

-- Even at the zero completion coordinate the original factor residue map is available.
example (s : S) :
    let AD0 := (boundedAboveCompletionCommMonFunctor R d).obj
      (boundedAboveCompletedTensorAlgebra R 0 S T)
    let C0 := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj AD0.X.obj
    letI := derivedH0CommRing AD0
    letI := derivedH0Algebra AD0
    iteratedTensorCartierLeftAlgHom R 0 d S T
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) s) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C0 d})
        (iteratedTensorH0LeftAlgHom R 0 d S T s) :=
  iteratedTensorCartierLeftAlgHom_mk R 0 d S T s
