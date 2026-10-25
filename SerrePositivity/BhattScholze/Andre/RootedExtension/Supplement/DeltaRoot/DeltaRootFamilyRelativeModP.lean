module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootFamilyRawRegular
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootRawRelativeCompletionModP

/-! # 任意根関係全族の実導来還元・完備化比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
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

/-- 任意根関係全族では、raw包のp正則性を内部で供給して実係数拡大の全高次Torが消える。 -/
theorem deltaRootFamilyRelativeModP_torVanishing
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
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η)) :
    scalarExtensionTorVanishing qA (ModuleCat.of A B) := by
  exact deltaRootRawRelativeModP_torVanishing D b hpA
    (deltaRootFamilyRaw_p_mul_injective (η := η) D b hpA w hw hg₀ hg₁)

/-- 任意根関係全族の実導来還元を実raw包/pへ同定する。raw包のp正則性は追加仮定しない。 -/
def deltaRootFamilyRelativeDerivedModPIso
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
    (boundedAboveDerivedBaseChange qA).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B)) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of QA (B ⧸ Ideal.span {(p : B)})) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  exact deltaRootRawRelativeDerivedModPIso D b hpA
    (deltaRootFamilyRaw_p_mul_injective (η := η) D b hpA w hw hg₀ hg₁) hg w hw

/-- 任意根関係全族の元のA上の実導来完備化のmod p比較。 -/
def deltaRootFamilyRelativeCompletedDerivedModPIso
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
    (boundedAboveDerivedBaseChange qA).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B))) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of QA (B ⧸ Ideal.span {(p : B)})) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  exact deltaRootRawRelativeCompletedDerivedModPIso D b hpA
    (deltaRootFamilyRaw_p_mul_injective (η := η) D b hpA w hw hg₀ hg₁) hg w hw

/-- 任意全族の実mod p同型は元のA上の標準実導来完備化単位と可換。 -/
theorem deltaRootFamilyRelativeCompletedDerivedModPIso_unit
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
    (boundedAboveDerivedBaseChange qA).map
        ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B))) ≫
      (deltaRootFamilyRelativeCompletedDerivedModPIso D b hpA w hw hg₀ hg₁ hg).hom =
        (deltaRootFamilyRelativeDerivedModPIso D b hpA w hw hg₀ hg₁ hg).hom := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  exact deltaRootRawRelativeCompletedDerivedModPIso_unit D b hpA
    (deltaRootFamilyRaw_p_mul_injective (η := η) D b hpA w hw hg₀ hg₁) hg w hw

end SerrePositivity.BhattScholze
