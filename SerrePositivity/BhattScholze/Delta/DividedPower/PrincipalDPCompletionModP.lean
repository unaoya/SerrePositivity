module

public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPModP
public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient

/-! # 正則分冪表示環上の実導来完備化のmod p比較

表示環R自身上の単位加群を扱う。A上のRの平坦性は仮定しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A] (y : A)
local notation "R₀" => PrincipalDPPresentation A y
local notation "I₀" => Ideal.span {(p : R₀)}
local notation "Q₀" => R₀ ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk I₀

/-- 表示環自身の単位加群には、p商への実係数拡大で高次Torは生じない。 -/
theorem principalDPUnitModP_torVanishing :
    scalarExtensionTorVanishing q₀ (ModuleCat.of R₀ R₀) := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
      exact ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R₀)).obj
        (baseChangeScalarModule q₀)).isZero_leftDerived_obj_projective_succ n (ModuleCat.of R₀ R₀)

/-- 表示環の単位加群の実係数拡大は、実商環R/pの単位加群。 -/
def principalDPUnitModPScalarEquiv :
    ((ModuleCat.extendScalars q₀).obj (ModuleCat.of R₀ R₀)) ≃ₗ[Q₀] Q₀ := by
  let : Algebra R₀ Q₀ := (q₀).toAlgebra
  exact TensorProduct.AlgebraTensorModule.rid R₀ Q₀ Q₀

/-- 単位加群の実導来p還元は、標準augmentationにより実p商の次数零対象と一致する。 -/
def principalDPUnitDerivedModPIso :
    (boundedAboveDerivedBaseChange q₀).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R₀ R₀)) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Q₀) :=
  boundedAboveDerivedBaseChangeModuleAugmentationIso _ _ (principalDPUnitModP_torVanishing y) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso (principalDPUnitModPScalarEquiv y).toModuleIso

variable [Fact p.Prime]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))

/-- 正則入力では、実導来p完備化の実導来p還元がR/pの次数零対象となる。 -/
def principalDPCompletedDerivedModPIso :
    (boundedAboveDerivedBaseChange q₀).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor R₀ (p : R₀)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R₀ R₀))) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Q₀) := by
  have hr : IsSMulRegular R₀ (p : R₀) := principalDPPresentation_p_mul_injective hA hpA y hy
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R₀ R₀)
  let F (b : R₀) :=
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).obj X ≅
      (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor R₀ (p : R₀)).obj X)
  have e : F ((p : R₀) ^ 1) :=
    DerivedCompletion.boundedAboveDerivedCompletionQuotientIso R₀ (p : R₀) hr 1 X
  have e' : F (p : R₀) := Eq.mp (congrArg F (_root_.pow_one (p : R₀))) e
  exact e'.symm ≪≫ principalDPUnitDerivedModPIso y

/-- 実導来完備化の実p還元は、既存の係数p商上の表示環にも具体的に同定される。 -/
def principalDPCompletedDerivedModPPresentationIso :
    letI := (principalDPModPEquiv p y).toRingHom.toAlgebra
    (boundedAboveDerivedBaseChange q₀).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor R₀ (p : R₀)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R₀ R₀))) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation (A ⧸ Ideal.span {(p : A)})
          (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))) := by
  letI := (principalDPModPEquiv p y).toRingHom.toAlgebra
  let e : Q₀ ≃ₐ[Q₀] PrincipalDPPresentation (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y) :=
    { principalDPModPEquiv p y with commutes' := fun _ ↦ rfl }
  exact principalDPCompletedDerivedModPIso y hA hpA hy ≪≫
    boundedAboveDerivedSingleFunctor.mapIso e.toLinearEquiv.toModuleIso

end SerrePositivity.BhattScholze
