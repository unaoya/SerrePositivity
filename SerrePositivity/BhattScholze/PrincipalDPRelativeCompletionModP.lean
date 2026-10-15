module

public import SerrePositivity.BhattScholze.PrincipalDPRelativeDerivedModP
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient

/-! # 元の係数環上の実導来完備化と具体的mod p表示環 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A] (y : A)
local notation "R₀" => PrincipalDPPresentation A y
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- Aのp正則性の下、標準A導来完備化単位を実p還元した射は同型。 -/
theorem principalDPRelativeCompletionUnit_modP_isIso
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) :
    IsIso ((boundedAboveDerivedBaseChange q₀).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)))) := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)
  have hr : IsSMulRegular A (p : A) := hpA
  let F (b : A) := IsIso ((boundedAboveDerivedBaseChange
    (Ideal.Quotient.mk (Ideal.span {b}))).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app X))
  have h : F ((p : A) ^ 1) :=
    DerivedCompletion.boundedAboveDerivedCompletion_quotient_unit_isIso A (p : A) hr 1 X
  exact Eq.mp (congrArg F (_root_.pow_one (p : A))) h

variable [Fact p.Prime]

/-- A上の実導来完備化を実p還元すると、係数A/p上の具体的表示環の次数零対象になる。 -/
def principalDPRelativeCompletedDerivedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    (boundedAboveDerivedBaseChange q₀).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀))) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)
  letI := principalDPRelativeCompletionUnit_modP_isIso y hpA
  exact (asIso ((boundedAboveDerivedBaseChange q₀).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app X))).symm ≪≫
    principalDPRelativeDerivedModPIso y hA hpA hy

/-- 実mod p比較は、元のA上の標準導来完備化単位と両立する。 -/
theorem principalDPRelativeCompletedDerivedModPIso_unit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    (boundedAboveDerivedBaseChange q₀).map
        ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀))) ≫
      (principalDPRelativeCompletedDerivedModPIso y hA hpA hy).hom =
        (principalDPRelativeDerivedModPIso y hA hpA hy).hom := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)
  let f := (boundedAboveDerivedBaseChange q₀).map
    ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app X)
  let := principalDPRelativeCompletionUnit_modP_isIso y hpA
  change (asIso f).hom ≫ ((asIso f).symm ≪≫
    principalDPRelativeDerivedModPIso y hA hpA hy).hom = _
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

end SerrePositivity.BhattScholze
