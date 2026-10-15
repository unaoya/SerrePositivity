module

public import SerrePositivity.BhattScholze.PrincipalDPRelativeModPKoszul
public import SerrePositivity.BhattScholze.PrincipalDPBaseChangeUniversal
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete

/-! # 元のA→A/pに沿う実導来分冪表示環比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A] (y : A)
local notation "R₀" => PrincipalDPPresentation A y
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 実係数拡大の通常加群は、任意係数への既存表示環同型で具体的に計算できる。 -/
def principalDPRelativeModPScalarEquiv :
    ((ModuleCat.extendScalars q₀).obj (ModuleCat.of A R₀)) ≃ₗ[Q₀]
      PrincipalDPPresentation Q₀ (q₀ y) :=
  (principalDPBaseChangeUniversalEquiv (B := Q₀) y).toLinearEquiv

variable [Fact p.Prime]

/-- 正則入力では、元のA→A/pへの表示環の全高次Torは零。A平坦性は仮定しない。 -/
theorem principalDPRelativeModP_torVanishing
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
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
      (principalDPRelativeDerivedModPRestrictedIso y hA hpA hy)
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

/-- 元のA→A/pで実導来還元した表示環は、係数p商上の具体的表示環の次数零対象。 -/
def principalDPRelativeDerivedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    (boundedAboveDerivedBaseChange q₀).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) :=
  boundedAboveDerivedBaseChangeModuleAugmentationIso _ _
      (principalDPRelativeModP_torVanishing y hA hpA hy) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso (principalDPRelativeModPScalarEquiv y).toModuleIso

end SerrePositivity.BhattScholze
