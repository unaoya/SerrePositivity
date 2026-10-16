import SerrePositivity.HomologicalAlgebra.PureDerivedCartierRepresentatives
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionAlgebraObjects
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.quotientBaseChangeH0Iso
assert_no_sorry SerrePositivity.derivedQuotientModuleIso_homology
assert_no_sorry SerrePositivity.quotientBaseChangeH0Iso_one_tmul
assert_no_sorry SerrePositivity.principalAdicReductionAlgEquiv
assert_no_sorry SerrePositivity.principalAdicReductionAlgEquiv_toAlgHom
assert_no_sorry SerrePositivity.principalAdicReductionAlgEquiv_mk
assert_no_sorry SerrePositivity.principalQuotientBaseChangeH0Iso
assert_no_sorry SerrePositivity.normalizedSingleCartierH0Iso
assert_no_sorry SerrePositivity.normalizedSingleCartierH0Iso_eq_standard
assert_no_sorry SerrePositivity.normalizedSingleCartierH0Iso_one_tmul
assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_single_representative
assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_single_map
assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_single_map_one

#print axioms SerrePositivity.quotientBaseChangeH0Iso
#print axioms SerrePositivity.derivedQuotientModuleIso_homology
#print axioms SerrePositivity.quotientBaseChangeH0Iso_one_tmul
#print axioms SerrePositivity.principalAdicReductionAlgEquiv
#print axioms SerrePositivity.principalAdicReductionAlgEquiv_toAlgHom
#print axioms SerrePositivity.principalAdicReductionAlgEquiv_mk
#print axioms SerrePositivity.principalQuotientBaseChangeH0Iso
#print axioms SerrePositivity.normalizedSingleCartierH0Iso
#print axioms SerrePositivity.normalizedSingleCartierH0Iso_eq_standard
#print axioms SerrePositivity.normalizedSingleCartierH0Iso_one_tmul
#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_single_representative
#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_single_map
#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_single_map_one

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
open scoped TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (p : ℕ) (d : R) (hd : IsSMulRegular R d)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "LS" => boundedAboveDerivedAlgebra (R := R) S
local notation "AP" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
local notation "FL" => boundedAboveCompletedTensorAlgebraLeft R (p : R) S T ≫
  boundedAboveCompletionAlgebraUnit R d AP
local notation "FR" => boundedAboveCompletedTensorAlgebraRight R (p : R) S T ≫
  boundedAboveCompletionAlgebraUnit R d AP

-- The literal original left factor map has the claimed value on each original representative.
example [(AD).X.obj.IsGE 0] [(AD).X.obj.IsLE 0]
    (hS : IsSMulRegular S d) (hC : IsSMulRegular C d) (s : S) :
    letI := derivedH0CommRing LS
    letI := derivedH0Algebra LS
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    let eS : ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (LS).X.obj) ≃ₐ[R] S :=
      derivedSingleH0AlgEquiv (R := R) S
    (pureDerivedAlgebraCartierQuotientH0Iso R d hd AD hC).hom
        ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {d})) 0).map
          (((boundedAboveDerivedBaseChange (q)).map (FL).hom.hom).hom)
          ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app (ModuleCat.of R S)
            ((1 : R ⧸ Ideal.span {d}) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] s))) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d}) (derivedH0AlgMap FL (eS.symm s)) :=
  pureDerivedAlgebraCartierQuotientH0Iso_single_map R d S hd hS AD hC FL s

-- The literal original right factor map retains the original unit Cartier class.
example [(AD).X.obj.IsGE 0] [(AD).X.obj.IsLE 0]
    (hT : IsSMulRegular T d) (hC : IsSMulRegular C d) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (pureDerivedAlgebraCartierQuotientH0Iso R d hd AD hC).hom
        ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {d})) 0).map
          (((boundedAboveDerivedBaseChange (q)).map (FR).hom.hom).hom)
          ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app (ModuleCat.of R T)
            ((1 : R ⧸ Ideal.span {d}) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] (1 : T)))) = 1 :=
  pureDerivedAlgebraCartierQuotientH0Iso_single_map_one R d T hd hT AD hC FR

-- A zero quotient base is included in the unconditional standard H⁰ computation.
example (M : ModuleCat.{u} R) (m : M) :
    (quotientBaseChangeH0Iso (⊤ : Ideal R) M).hom
        ((boundedAboveDerivedBaseChangeModuleH0Iso (Ideal.Quotient.mk (⊤ : Ideal R))).inv.app M
          ((1 : R ⧸ (⊤ : Ideal R)) ⊗ₜ[R, Ideal.Quotient.mk (⊤ : Ideal R)] m)) =
      ((⊤ : Ideal R) • (⊤ : Submodule R M)).mkQ m :=
  quotientBaseChangeH0Iso_one_tmul (⊤ : Ideal R) M m
