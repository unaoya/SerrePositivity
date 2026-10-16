module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarConePurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.PerfectRingTor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionAlgebraObjects
public import SerrePositivity.HomologicalAlgebra.DerivedH0Algebra
/-! # Completed tensor products with perfect mod-p residues

The original completed derived tensor is discrete and p-torsion-free when the
base and both factors are p-regular and their ordinary residues are perfect.
The residue tensor is not assumed flat over the residue base.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
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

/-- The original module tensor completion is discrete with injective p action on H0. -/
lemma completedTensor_pure_of_perfect_residue
    [hRq : PerfectRing Rq p] [hSq : PerfectRing Sq p] [hTq : PerfectRing Tq p]
    (ha : IsSMulRegular R (p : R))
    (hS : IsSMulRegular (ModuleCat.of R S) (p : R))
    (hT : IsSMulRegular (ModuleCat.of R T) (p : R)) :
    let X := (boundedAboveDerivedCompletionFunctor R (p : R)).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S),
          boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧ Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj => (p : R) • x) := by
  let X0 := boundedAboveDerivedTensor.obj
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S),
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))
  let X := (boundedAboveDerivedCompletionFunctor R (p : R)).obj X0
  apply derived_pure_of_complete_regular_quotient_pure (p : R) ha X
    (derivedComplexCompletionFunctor_isComplete R (p : R) X0.obj)
  intro i hi
  have hSacyc := scalarExtensionTorVanishing_principal_of_regular (p : R) ha
    (ModuleCat.of R S) hS
  have hTacyc := scalarExtensionTorVanishing_principal_of_regular (p : R) ha
    (ModuleCat.of R T) hT
  let q := Ideal.Quotient.mk Ip
  let ec : (boundedAboveDerivedBaseChange q).obj X ≅
      (boundedAboveDerivedBaseChange q).obj X0 := by
    have e := (boundedAboveDerivedCompletionQuotientIso R (p : R) ha 1 X0).symm
    rw [pow_one] at e
    exact e
  let eq := derivedTensorQuotientAlgebraIso Ip S T hSacyc hTacyc
  have hpq : (p : Rq) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Ip)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have haug : IsIso (boundedAboveDerivedTensorAlgebraAugmentation (R := Rq) Sq Tq).hom.hom :=
    @perfectRing_derivedTensorAlgebraAugmentation_isIso_of_char_eq_zero p _ Rq _ hRq hpq
      Sq _ (adicQuotientAlgebra Ip S) hSq Tq _ (adicQuotientAlgebra Ip T) hTq
  have := haug
  let aug := (boundedAboveDerivedTensorAlgebraAugmentation (R := Rq) Sq Tq).hom.hom
  let ea := DerivedCategory.Minus.ι.mapIso (asIso aug)
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat Rq) i).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Rq Sq),
          boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Rq Tq))).obj) := by
    exact (derivedSingleHomology_isZero (ModuleCat.of Rq (Sq ⊗[Rq] Tq)) i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat Rq) i).mapIso ea)
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Rq) i).mapIso
    (DerivedCategory.Minus.ι.mapIso (ec ≪≫ eq)))

/-- The same purity applies to the original completed commutative algebra object. -/
lemma completedTensorAlgebra_pure_of_perfect_residue
    [PerfectRing Rq p] [PerfectRing Sq p] [PerfectRing Tq p]
    (ha : IsSMulRegular R (p : R))
    (hS : IsSMulRegular (ModuleCat.of R S) (p : R))
    (hT : IsSMulRegular (ModuleCat.of R T) (p : R)) :
    let X := (boundedAboveCompletedTensorAlgebra R (p : R) S T).X
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧ Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj => (p : R) • x) := by
  exact completedTensor_pure_of_perfect_residue p R S T ha hS hT

/-- Multiplication by p on the actual H0 ring is injective. -/
lemma completedTensorH0_p_mul_injective_of_perfect_residue
    [PerfectRing Rq p] [PerfectRing Sq p] [PerfectRing Tq p]
    (ha : IsSMulRegular R (p : R))
    (hS : IsSMulRegular (ModuleCat.of R S) (p : R))
    (hT : IsSMulRegular (ModuleCat.of R T) (p : R)) :
    let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
    let := derivedH0CommRing A
    Function.Injective (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj =>
      (p : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) * x) := by
  let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  have hreg := (completedTensorAlgebra_pure_of_perfect_residue p R S T ha hS hT).2.2
  change Function.Injective (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj =>
    (p : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) * x)
  intro x y hxy
  apply hreg
  change (p : R) • x = (p : R) • y
  simpa only [Algebra.smul_def, map_natCast] using hxy

/-- The actual H0 ring is classically p-adically complete. -/
lemma completedTensorH0_isAdicComplete_of_perfect_residue
    [PerfectRing Rq p] [PerfectRing Sq p] [PerfectRing Tq p]
    (ha : IsSMulRegular R (p : R))
    (hS : IsSMulRegular (ModuleCat.of R S) (p : R))
    (hT : IsSMulRegular (ModuleCat.of R T) (p : R)) :
    let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
    let := derivedH0CommRing A
    IsAdicComplete
      (Ideal.span {(p : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj)})
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) := by
  let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
  let H := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  have hc : IsComplete R (p : R) A.X.obj :=
    derivedComplexCompletionFunctor_isComplete R (p : R) _
  have hH := isComplete_homology_isModuleComplete R (p : R) A.X.obj hc 0
  have hreg := (completedTensorAlgebra_pure_of_perfect_residue p R S T ha hS hT).2.2
  have hAH : IsAdicComplete Ip H :=
    (isModuleComplete_iff_isAdicComplete_of_regular R (p : R) H hreg).mp hH
  change IsAdicComplete (Ideal.span {(p : H)}) H
  have hself :=
    (IsAdicComplete.map_algebraMap_iff (I := Ip) (S := H) (M := H)).mpr hAH
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hself
end SerrePositivity.DerivedCompletion
