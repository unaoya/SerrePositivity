import SerrePositivity.HomologicalAlgebra.PureDerivedCartierNaturality
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionAlgebraObjects
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.principalAdicReductionAlgHom
assert_no_sorry SerrePositivity.principalAdicReductionAlgHom_toLinearMap
assert_no_sorry SerrePositivity.principalAdicReductionAlgHom_mk
assert_no_sorry SerrePositivity.principalAdicReductionEquiv_naturality
assert_no_sorry SerrePositivity.pureDerivedAlgebraSingleIso
assert_no_sorry SerrePositivity.pureDerivedAlgebraSingleIso_naturality
assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientIso_naturality
assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_naturality
assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_algHom_naturality

#print axioms SerrePositivity.principalAdicReductionAlgHom
#print axioms SerrePositivity.principalAdicReductionAlgHom_toLinearMap
#print axioms SerrePositivity.principalAdicReductionAlgHom_mk
#print axioms SerrePositivity.principalAdicReductionEquiv_naturality
#print axioms SerrePositivity.pureDerivedAlgebraSingleIso
#print axioms SerrePositivity.pureDerivedAlgebraSingleIso_naturality
#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientIso_naturality
#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_naturality
#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_algHom_naturality

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (p : ℕ) (d : R) (hd : IsSMulRegular R d)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "LS" => boundedAboveDerivedAlgebra (R := R) S
local notation "AP" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
local notation "F" => boundedAboveCompletedTensorAlgebraLeft R (p : R) S T ≫
  boundedAboveCompletionAlgebraUnit R d AP
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})

-- Apply the naturality square to the original left factor and the original second unit.
example [(AD).X.obj.IsGE 0] [(AD).X.obj.IsLE 0]
    (hS : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (LS).X.obj) d)
    (hC : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj) d) :
    letI hge : (LS).X.obj.IsGE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
      infer_instance
    letI hle : (LS).X.obj.IsLE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
      infer_instance
    letI := derivedH0CommRing LS
    letI := derivedH0Algebra LS
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {d})) 0).map
        (((boundedAboveDerivedBaseChange (q)).map (F).hom.hom).hom) ≫
        (pureDerivedAlgebraCartierQuotientH0Iso R d hd AD hC).hom =
      (pureDerivedAlgebraCartierQuotientH0Iso R d hd LS hS).hom ≫
        ModuleCat.ofHom (principalAdicReductionAlgHom R d (derivedH0AlgMap F)).toLinearMap := by
  let hge : (LS).X.obj.IsGE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
    infer_instance
  let hle : (LS).X.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
    infer_instance
  exact pureDerivedAlgebraCartierQuotientH0Iso_algHom_naturality R d hd
    (A := LS) (B := AD) F hS hC

-- The coefficient quotient may be the zero ring; no nonunit hypothesis is required.
example (f : S →ₐ[R] T) (s : S) :
    principalAdicReductionAlgHom R 1 f
        (Ideal.Quotient.mk (Ideal.span {algebraMap R S (1 : R)}) s) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R T (1 : R)}) (f s) :=
  principalAdicReductionAlgHom_mk R 1 f s
