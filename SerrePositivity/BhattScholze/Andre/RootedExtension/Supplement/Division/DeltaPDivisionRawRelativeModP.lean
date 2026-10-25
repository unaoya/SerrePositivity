module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaPDivisionRawPrincipal
public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPRelativeCompletionModP

/-! # raw δ p除算包の元のA上の実mod p・導来完備化比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 正則一元raw包には、元のA→A/pへの実係数拡大で高次Torが生じない。 -/
theorem deltaPDivisionRawRelativeModP_torVanishing
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    scalarExtensionTorVanishing q₀ (ModuleCat.of A B₀) := by
  intro n hn
  let e := (deltaPDivisionRawPrincipalAlgEquiv (σ := σ)
      hA hpA D y hg v hv hy).toLinearEquiv.toModuleIso
  have hz := principalDPRelativeModP_torVanishing y hA hpA hy n hn
  exact IsZero.of_iso hz
    (((Tor (ModuleCat.{u} A) n).obj (baseChangeScalarModule q₀)).mapIso e)

/-- 元のA→A/pへのraw包の実導来還元を、具体的な分冪表示環へ同定する。 -/
def deltaPDivisionRawRelativeDerivedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    (boundedAboveDerivedBaseChange q₀).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀)) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) :=
  (boundedAboveDerivedBaseChange q₀).mapIso
      (boundedAboveDerivedSingleFunctor.mapIso
        (deltaPDivisionRawPrincipalAlgEquiv (σ := σ)
      hA hpA D y hg v hv hy).toLinearEquiv.toModuleIso) ≪≫
    principalDPRelativeDerivedModPIso y hA hpA hy

/-- 元のA上のraw包の実導来完備化も、実p還元後は具体的な表示環となる。 -/
def deltaPDivisionRawRelativeCompletedDerivedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    (boundedAboveDerivedBaseChange q₀).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀))) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) :=
  (boundedAboveDerivedBaseChange q₀).mapIso
      ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).mapIso
        (boundedAboveDerivedSingleFunctor.mapIso
          (deltaPDivisionRawPrincipalAlgEquiv (σ := σ)
      hA hpA D y hg v hv hy).toLinearEquiv.toModuleIso)) ≪≫
    principalDPRelativeCompletedDerivedModPIso y hA hpA hy

/-- raw包の実mod p比較は、元のA上の標準導来完備化単位と両立する。 -/
theorem deltaPDivisionRawRelativeCompletedDerivedModPIso_unit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    (boundedAboveDerivedBaseChange q₀).map
        ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀))) ≫
      (deltaPDivisionRawRelativeCompletedDerivedModPIso D y hA hpA hg v hv hy).hom =
        (deltaPDivisionRawRelativeDerivedModPIso D y hA hpA hg v hv hy).hom := by
  let e := boundedAboveDerivedSingleFunctor.mapIso
    (deltaPDivisionRawPrincipalAlgEquiv (σ := σ)
      hA hpA D y hg v hv hy).toLinearEquiv.toModuleIso
  let F := boundedAboveDerivedBaseChange q₀
  let C := DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
  let U := DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
  change F.map (U.app _) ≫
      (F.map (C.map e.hom) ≫ (principalDPRelativeCompletedDerivedModPIso y hA hpA hy).hom) =
    F.map e.hom ≫ (principalDPRelativeDerivedModPIso y hA hpA hy).hom
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ← U.naturality e.hom,
    CategoryTheory.Functor.map_comp, Category.assoc,
    principalDPRelativeCompletedDerivedModPIso_unit]
  rfl

end SerrePositivity.BhattScholze
