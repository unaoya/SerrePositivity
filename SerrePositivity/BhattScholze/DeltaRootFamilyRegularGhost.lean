module

public import SerrePositivity.BhattScholze.DeltaRootFamilyCompletedModPFlat
public import SerrePositivity.BhattScholze.DeltaRootSourceRegularGhost

/-! # G4による任意根族の外部ghost仮定の解消 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard deltaRootRawCoefficientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "B" =>
  DeltaAdjoinDivision E (p : P) (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "QA" => A ⧸ Ideal.span {(p : A)}
local notation "qA" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qA)
  (CategoryTheory.Functor.obj (DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A))
    (CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor (ModuleCat.of A B)))

private theorem finiteSourceGhost
    (hpA : Function.Injective (fun z : A => (p : A) * z)) (T : Finset σ) :
    Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T) := by
  have hpP : IsSMulRegular P (p : P) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)
  have hpL : IsSMulRegular (RelativeFreeDeltaRing (R := P) T)
      (p : RelativeFreeDeltaRing (R := P) T) := by
    simpa only [map_natCast] using hpP.of_flat (S := RelativeFreeDeltaRing (R := P) T)
  exact witt_ghostMap_injective_of_mul_prime_injective p _ hpL

private theorem nextSourceGhost (T : Finset σ)
    (hpB : Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
      (fun t : T => DeltaStructure.frobeniusLift E (r t)) =>
      (p : DeltaAdjoinDivision E (p : P)
        (fun t : T => DeltaStructure.frobeniusLift E (r t))) * z)) :
    Function.Injective (WittVector.ghostMap : WittVector p
      (RelativeFreeDeltaRing (R := DeltaAdjoinDivision E (p : P)
        (fun t : T => DeltaStructure.frobeniusLift E (r t))) PUnit.{u+1}) → ℕ →
      RelativeFreeDeltaRing (R := DeltaAdjoinDivision E (p : P)
        (fun t : T => DeltaStructure.frobeniusLift E (r t))) PUnit.{u+1}) := by
  let C := DeltaAdjoinDivision E (p : P)
    (fun t : T => DeltaStructure.frobeniusLift E (r t))
  have hpL : IsSMulRegular (RelativeFreeDeltaRing (R := C) PUnit.{u+1})
      (p : RelativeFreeDeltaRing (R := C) PUnit.{u+1}) := by
    have h := (show IsSMulRegular C (p : C) from hpB).of_flat
      (S := RelativeFreeDeltaRing (R := C) PUnit.{u+1})
    rw [map_natCast (algebraMap C (RelativeFreeDeltaRing (R := C) PUnit.{u+1})) p] at h
    exact h
  exact witt_ghostMap_injective_of_mul_prime_injective p _ hpL

/-- 任意根族のraw p除算包のp正則性。外部ghost仮定は不要。 -/
theorem deltaRootFamilyRaw_p_mul_injective_of_p_regular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    Function.Injective (fun z : B => (p : B) * z) :=
  deltaRootFamilyRaw_p_mul_injective (η := PUnit.{u+1}) D b hpA w hw
    (finiteSourceGhost hpA) (nextSourceGhost D b)

/-- 任意根族の実p完備化の標準mod p還元の非零次数消滅。 -/
theorem deltaRootFamilyCompletedModP_homology_isZero_of_p_regular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat QA) i).obj (Y).obj) :=
  deltaRootFamilyCompletedModP_homology_isZero (η := PUnit.{u+1}) D b hpA w hw
    (finiteSourceGhost hpA) (nextSourceGhost D b)
    (deltaRootSource_ghostMap_injective (σ := σ) hpA) i hi

/-- 任意根族の実p完備化の標準mod p還元H0は、追加ghost仮定なしに忠実平坦。 -/
theorem deltaRootFamilyCompletedModPH0_faithfullyFlat_of_p_regular
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    Module.FaithfullyFlat QA
      ((DerivedCategory.homologyFunctor (ModuleCat QA) 0).obj (Y).obj) :=
  deltaRootFamilyCompletedModPH0_moduleFaithfullyFlat (η := PUnit.{u+1}) D b hpA w hw
    (finiteSourceGhost hpA) (nextSourceGhost D b)
    (deltaRootSource_ghostMap_injective (σ := σ) hpA)

end SerrePositivity.BhattScholze
