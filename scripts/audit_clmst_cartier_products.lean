import SerrePositivity.HomologicalAlgebra.DerivedTensorCartierProducts
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_tensor_representative
assert_no_sorry SerrePositivity.derivedTensorAlgebraMap_tmul
assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_tensor_representative_mul

#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_tensor_representative
#print axioms SerrePositivity.derivedTensorAlgebraMap_tmul
#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_tensor_representative_mul

noncomputable section
universe u
open CategoryTheory SerrePositivity
open scoped TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (d : R) (hd : IsSMulRegular R d)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0]
local notation "B" => boundedAboveDerivedTensorAlgebra (R := R) S T
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})

-- The original normalized tensor unit retains its original Cartier unit.
theorem audit_cartier_tensor_unit
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hA : IsSMulRegular H d) (u : B ⟶ A) :
    letI := derivedH0CommRing B
    letI := derivedH0Algebra B
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    (pureDerivedAlgebraCartierQuotientH0Iso R d hd A hA).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (((boundedAboveDerivedBaseChange (q)).map u.hom.hom).hom)
          ((derivedTensorQuotientBaseChangeH0Iso (Ideal.span {d}) S T hS hT).inv
            ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] ((1 : S) ⊗ₜ[R] (1 : T))))) = 1 := by
  let := derivedH0CommRing B
  let := derivedH0Algebra B
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  have h := pureDerivedAlgebraCartierQuotientH0Iso_tensor_representative R d hd S T A
    hS hT hA u 1 1
  simp only [← Algebra.TensorProduct.one_def, map_one] at h
  exact h

-- A zero representative still gives zero, with no regularity hypothesis on the source tensor.
theorem audit_cartier_tensor_zero
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hA : IsSMulRegular H d) (u : B ⟶ A) (t : T) :
    letI := derivedH0CommRing B
    letI := derivedH0Algebra B
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    (pureDerivedAlgebraCartierQuotientH0Iso R d hd A hA).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (((boundedAboveDerivedBaseChange (q)).map u.hom.hom).hom)
          ((derivedTensorQuotientBaseChangeH0Iso (Ideal.span {d}) S T hS hT).inv
            ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] ((0 : S) ⊗ₜ[R] t)))) = 0 := by
  let := derivedH0CommRing B
  let := derivedH0Algebra B
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  have h := pureDerivedAlgebraCartierQuotientH0Iso_tensor_representative R d hd S T A
    hS hT hA u 0 t
  simp only [TensorProduct.zero_tmul, map_zero] at h
  simpa only [TensorProduct.zero_tmul] using h

assert_no_sorry audit_cartier_tensor_unit
assert_no_sorry audit_cartier_tensor_zero
#print axioms audit_cartier_tensor_unit
#print axioms audit_cartier_tensor_zero
