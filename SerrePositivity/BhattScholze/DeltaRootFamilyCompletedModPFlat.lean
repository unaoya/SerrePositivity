module

public import SerrePositivity.BhattScholze.DeltaRootFamilyRelativeModP
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # 任意根関係raw包の実導来完備化のmod pホモロジーと忠実平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard deltaRootRawCoefficientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ η : Type u} [CommRing A] [Unique η]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "B" =>
  DeltaAdjoinDivision E (p : P) (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "QA" => A ⧸ Ideal.span {(p : A)}
local notation "qA" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- A上の実導来完備化の実p還元H0は、標準A/p作用付き実raw包/pと線形同値。 -/
def deltaRootFamilyCompletedModPH0Equiv
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
        WittVector p (RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
        ℕ → RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ)) :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} QA) 0).obj
      (((boundedAboveDerivedBaseChange qA).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)))).obj)) ≃ₗ[QA]
      (B ⧸ Ideal.span {(p : B)}) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let e := DerivedCategory.Minus.ι.mapIso
    (deltaRootFamilyRelativeCompletedDerivedModPIso D b hpA w hw hg₀ hg₁ hg)
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} QA) 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} QA) 0).app
      (ModuleCat.of QA (B ⧸ Ideal.span {(p : B)}))).toLinearEquiv

/-- この実p還元は全ての非零次数で実ホモロジーが零。 -/
theorem deltaRootFamilyCompletedModP_homology_isZero
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
        WittVector p (RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
        ℕ → RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} QA) i).obj
      (((boundedAboveDerivedBaseChange qA).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)))).obj)) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let e := (DerivedCategory.homologyFunctor (ModuleCat.{u} QA) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (deltaRootFamilyRelativeCompletedDerivedModPIso D b hpA w hw hg₀ hg₁ hg))
  exact IsZero.of_iso
    (derivedSingleHomology_isZero (ModuleCat.of QA (B ⧸ Ideal.span {(p : B)})) i hi) e

/-- 元のA上の実導来完備化をA→A/pで実還元したH0はA/p上忠実平坦。 -/
theorem deltaRootFamilyCompletedModPH0_moduleFaithfullyFlat
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
        WittVector p (RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
        ℕ → RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ)) :
    Module.FaithfullyFlat QA ((DerivedCategory.homologyFunctor (ModuleCat.{u} QA) 0).obj
      (((boundedAboveDerivedBaseChange qA).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)))).obj)) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  let := deltaRootRawModP_moduleFaithfullyFlat D b hpA hg w hw
  exact Module.FaithfullyFlat.of_linearEquiv QA (B ⧸ Ideal.span {(p : B)})
    (deltaRootFamilyCompletedModPH0Equiv D b hpA w hw hg₀ hg₁ hg)

end SerrePositivity.BhattScholze
