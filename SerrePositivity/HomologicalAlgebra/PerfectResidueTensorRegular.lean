module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
/-! # Regularity of p on the ordinary tensor with perfect residues

The negative first homology of its original Koszul reduction vanishes by C1.
No completion or flatness hypothesis is required for this ordinary tensor statement.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open DerivedCompletion
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
  [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "Ip" => Ideal.span {(p : R)}
local notation "Rq" => R ⧸ Ip
local notation "Sq" => S ⧸ Ideal.map (algebraMap R S) Ip
local notation "Tq" => T ⧸ Ideal.map (algebraMap R T) Ip

/-- Regularity and perfect residues of all three rings force p to be regular on the tensor. -/
lemma tensor_p_mul_injective_of_perfect_residue
    [hRq : PerfectRing Rq p] [hSq : PerfectRing Sq p] [hTq : PerfectRing Tq p]
    (ha : IsSMulRegular R (p : R))
    (hS : IsSMulRegular (ModuleCat.of R S) (p : R))
    (hT : IsSMulRegular (ModuleCat.of R T) (p : R)) :
    Function.Injective (fun x : S ⊗[R] T => (p : S ⊗[R] T) * x) := by
  let X := boundedAboveDerivedTensor.obj
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S),
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))
  let q := Ideal.Quotient.mk Ip
  let eq := derivedTensorQuotientAlgebraIso Ip S T
    (scalarExtensionTorVanishing_principal_of_regular (p : R) ha (ModuleCat.of R S) hS)
    (scalarExtensionTorVanishing_principal_of_regular (p : R) ha (ModuleCat.of R T) hT)
  have hpq : (p : Rq) = 0 := by
    rw [← map_natCast q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have haug : IsIso (boundedAboveDerivedTensorAlgebraAugmentation (R := Rq) Sq Tq).hom.hom :=
    @perfectRing_derivedTensorAlgebraAugmentation_isIso_of_char_eq_zero p _ Rq _ hRq hpq
      Sq _ (adicQuotientAlgebra Ip S) hSq Tq _ (adicQuotientAlgebra Ip T) hTq
  have := haug
  let aug := (boundedAboveDerivedTensorAlgebraAugmentation (R := Rq) Sq Tq).hom.hom
  let eqA := DerivedCategory.Minus.ι.mapIso eq ≪≫
    DerivedCategory.Minus.ι.mapIso (asIso aug)
  have hq : IsZero ((DerivedCategory.homologyFunctor (ModuleCat Rq) (-1)).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj) :=
    (derivedSingleHomology_isZero (ModuleCat.of Rq (Sq ⊗[Rq] Tq)) (-1) (by omega)).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat Rq) (-1)).mapIso eqA)
  let ec := (DerivedCategory.homologyFunctor (ModuleCat R) (-1)).mapIso
      (restrictedDerivedQuotientKoszulIso (p : R) ha X).symm ≪≫
    (derivedRestrictScalarsHomologyIso q (-1)).app
      ((boundedAboveDerivedBaseChange q).obj X).obj
  have hcone := ((ModuleCat.restrictScalars q).map_isZero hq).of_iso ec
  have hreg := derived_homology_smul_injective_of_scalarCone_isZero (p : R) X.obj 0
    (by simpa using hcone)
  let e := ((boundedAboveDerivedTensorModuleH0NatIso (ModuleCat.of R S)).app
    (ModuleCat.of R T)).toLinearEquiv
  intro x y hxy
  apply e.symm.injective
  apply hreg
  change (p : R) • e.symm x = (p : R) • e.symm y
  have hsmul : (p : R) • x = (p : R) • y := by
    simpa only [Algebra.smul_def, map_natCast] using hxy
  rw [← e.symm.map_smul, ← e.symm.map_smul, hsmul]
end SerrePositivity
