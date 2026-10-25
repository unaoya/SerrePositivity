module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaPDivisionRawRelativeModP
public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPQuotientFlat
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # raw包の実導来完備化のp還元ホモロジーと相対平坦性 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "B₀" => DeltaAdjoinDivision D (p : A) (fun _ : σ ↦ D.frobeniusLift y)
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 元のA上のraw包の実完備化をp還元した実H0は、具体的表示環とA/p線形同値。 -/
def deltaPDivisionRawCompletedModPH0Equiv
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) 0).obj
      (((boundedAboveDerivedBaseChange q₀).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀)))).obj)) ≃ₗ[Q₀]
      PrincipalDPPresentation Q₀ (q₀ y) := by
  let e := DerivedCategory.Minus.ι.mapIso
    (deltaPDivisionRawRelativeCompletedDerivedModPIso D y hA hpA hg v hv hy)
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} Q₀) 0).app
      (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y)))).toLinearEquiv

/-- この実p還元の全非零次数ホモロジーは零。 -/
theorem deltaPDivisionRawCompletedModP_homology_isZero
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) i).obj
      (((boundedAboveDerivedBaseChange q₀).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀)))).obj)) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (deltaPDivisionRawRelativeCompletedDerivedModPIso D y hA hpA hg v hv hy))
  exact IsZero.of_iso
    (derivedSingleHomology_isZero (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) i hi) e

/-- 任意のK→A/p作用に対し、p乗商のK平坦性から実完備化のp還元H0のK平坦性を得る。 -/
theorem deltaPDivisionRawCompletedModPH0_flat_of_powerQuotient_flat
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
    {K : Type v} [CommRing K] [Algebra K Q₀]
    (hQ : Module.Flat K (Q₀ ⧸ Ideal.span {(q₀ y) ^ p})) :
    Module.Flat K ((ModuleCat.restrictScalars (algebraMap K Q₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) 0).obj
        (((boundedAboveDerivedBaseChange q₀).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀)))).obj))) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) 0).obj
    (((boundedAboveDerivedBaseChange q₀).obj
          ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A B₀)))).obj)
  let : Module K M := Module.compHom M (algebraMap K Q₀)
  let : IsScalarTower K Q₀ M := IsScalarTower.of_compHom K Q₀ M
  have hpQ : (p : Q₀) = 0 := by
    change Ideal.Quotient.mk _ (p : A) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  let := principalDPPresentation_flat_of_quotient_flat
    (A := K) (Fact.out : p.Prime) hpQ (q₀ y) hQ
  exact Module.Flat.of_linearEquiv
    ((deltaPDivisionRawCompletedModPH0Equiv D y hA hpA hg v hv hy).restrictScalars K)

end SerrePositivity.BhattScholze
