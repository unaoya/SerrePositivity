import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedTensorCartierProducts
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.iteratedCompletedTensorCartierH0Iso_unit_tmul
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedCompletedTensorCartierH0Iso_eq_algHom
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensorCartierCompletedAlgEquiv
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensorCartierCompletedAlgEquiv_toAlgHom
assert_no_sorry SerrePositivity.DerivedCompletion.iteratedTensorCartierCompletedAlgEquiv_toLinearEquiv

#print axioms SerrePositivity.DerivedCompletion.iteratedCompletedTensorCartierH0Iso_unit_tmul
#print axioms SerrePositivity.DerivedCompletion.iteratedCompletedTensorCartierH0Iso_eq_algHom
#print axioms SerrePositivity.DerivedCompletion.iteratedTensorCartierCompletedAlgEquiv
#print axioms SerrePositivity.DerivedCompletion.iteratedTensorCartierCompletedAlgEquiv_toAlgHom
#print axioms SerrePositivity.DerivedCompletion.iteratedTensorCartierCompletedAlgEquiv_toLinearEquiv

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (a d : R) (hd : IsSMulRegular R d)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "AP" => boundedAboveCompletedTensorAlgebra R a S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
set_option quotPrecheck false in
local notation "CQ" => C ⧸ Ideal.span {algebraMap R C d}
local notation "RX" => boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ
set_option quotPrecheck false in
local notation "RC" => (boundedAboveCompletionCommMonFunctor Q ((q) a)).obj RX

-- The original canonical algebra map has an inverse on the original completed H⁰ ring.
theorem audit_cartier_original_inverse
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d) (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hp :
      letI := derivedH0CommRing AD
      letI := derivedH0Algebra AD
      letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
      IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ)) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    ∀ y : CQ, iteratedTensorCartierCompletedAlgHom R a d S T hp
      ((iteratedTensorCartierCompletedAlgEquiv R a d hd S T hS hT hC hpure hp).symm y) = y := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let : Algebra Q CQ := principalAdicQuotientAlgebra d C
  let := derivedH0CommRing RC
  let := derivedH0Algebra RC
  intro y
  exact (iteratedTensorCartierCompletedAlgEquiv R a d hd S T hS hT hC hpure hp).apply_symm_apply y

-- This inverse is also the original inverse of the established linear Cartier comparison.
theorem audit_cartier_linear_inverse
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d) (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hp :
      letI := derivedH0CommRing AD
      letI := derivedH0Algebra AD
      letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
      IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ)) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    ∀ y : CQ, (iteratedTensorCartierCompletedAlgEquiv R a d hd S T hS hT hC hpure hp).symm y =
      (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).inv y := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let : Algebra Q CQ := principalAdicQuotientAlgebra d C
  let := derivedH0CommRing RC
  let := derivedH0Algebra RC
  dsimp only
  intro y
  exact congrArg (fun e :
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RC).X.obj ≃ₗ[Q] CQ => e.symm y)
    (iteratedTensorCartierCompletedAlgEquiv_toLinearEquiv R a d hd S T hS hT hC hpure hp)

#print axioms audit_cartier_original_inverse
#print axioms audit_cartier_linear_inverse
assert_no_sorry audit_cartier_original_inverse
assert_no_sorry audit_cartier_linear_inverse
