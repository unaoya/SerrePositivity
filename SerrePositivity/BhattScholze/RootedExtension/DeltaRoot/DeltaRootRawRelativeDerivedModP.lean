module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootRawRelativeModPKoszul
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete

/-! # 元のA→A/pに沿う根関係raw包の高次Tor消滅と実導来比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard deltaRootRawCoefficientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "inputs" =>
  fun s ↦ DeltaStructure.frobeniusLift E (deltaRootRelationFamily (p := p) b s)
local notation "R₀" => DeltaAdjoinDivision E (p : P) inputs
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- Aとraw包がp正則なら、元の係数環A→A/pへの実係数拡大で全高次Torは消える。 -/
theorem deltaRootRawRelativeModP_torVanishing
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hpB : Function.Injective (fun a : R₀ ↦ (p : R₀) * a)) :
    scalarExtensionTorVanishing q₀ (ModuleCat.of A R₀) := by
  change (∀ n : ℕ, 0 < n → IsZero
    (((Tor (ModuleCat.{u} A) n).obj (baseChangeScalarModule q₀)).obj (ModuleCat.of A R₀)))
  rw [← derivedModuleBaseChange_negative_homology_vanishes_iff q₀ (ModuleCat.of A R₀)]
  intro n hn
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)
  let Y := (boundedAboveDerivedBaseChange q₀).obj X
  have hni : -(n : ℤ) ≠ 0 :=
    neg_ne_zero.mpr (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn))
  let e : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
      (((boundedAboveDerivedRestrictScalars q₀).obj Y).obj)) ≅
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
        ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
          (ModuleCat.of A (R₀ ⧸ Ideal.span {(p : R₀)})))) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).mapIso
      (deltaRootRawRelativeDerivedModPRestrictedIso D b hpA hpB)
  have ht : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
      ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
        (ModuleCat.of A (R₀ ⧸ Ideal.span {(p : R₀)})))) :=
    derivedSingleHomology_isZero _ (-(n : ℤ)) hni
  have hs : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
      (((boundedAboveDerivedRestrictScalars q₀).obj Y).obj)) := e.isZero_iff.mpr ht
  have hr := (derivedRestrictScalarsHomologyIso q₀ (-(n : ℤ))).app Y.obj
  have hs' : IsZero ((ModuleCat.restrictScalars q₀).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).obj Y.obj)) :=
    hr.isZero_iff.mp hs
  let : Subsingleton
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).obj Y.obj) :=
    ModuleCat.subsingleton_of_isZero (R := A) hs'
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).obj
      Y.obj) := ModuleCat.isZero_of_subsingleton
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).obj Y.obj)
  exact IsZero.of_iso hz
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).mapIso
      (boundedAboveDerivedBaseChangeModuleIso q₀ (ModuleCat.of A R₀))).symm

/-- 実係数拡大の通常加群は、標準A/p作用を持つ実raw p商と線形同型。 -/
def deltaRootRawRelativeModPScalarEquiv
    (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    ((ModuleCat.extendScalars q₀).obj (ModuleCat.of A R₀)) ≃ₗ[Q₀]
      (R₀ ⧸ Ideal.span {(p : R₀)}) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  exact (deltaRootRawBaseChangeModPAlgEquiv D b hpA hg w hw).toLinearEquiv

/-- 元のA→A/pに沿う実導来還元は、実raw包/pの標準A/p加群の次数零対象。 -/
def deltaRootRawRelativeDerivedModPIso
    (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
    (hpB : Function.Injective (fun x : R₀ ↦ (p : R₀) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
        ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A)) :
    letI := deltaRootRawModPBaseAlgebra D b hpA hg w hw
    (boundedAboveDerivedBaseChange q₀).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (R₀ ⧸ Ideal.span {(p : R₀)})) := by
  let := deltaRootRawModPBaseAlgebra D b hpA hg w hw
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso _ _
      (deltaRootRawRelativeModP_torVanishing D b hpA hpB) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso
      (deltaRootRawRelativeModPScalarEquiv D b hpA hg w hw).toModuleIso

end SerrePositivity.BhattScholze
