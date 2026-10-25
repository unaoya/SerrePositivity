module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionNormalizedDirectLimitModule
public import SerrePositivity.CommutativeAlgebra.ModuleDirectLimitFlat
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

/-! # BSの具体的全段正規化環の共通係数商上の平坦性 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ)
attribute [local instance] deltaDivisionFiniteNormalizedBaseAlgebra
  deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra
local notation "B" => (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)

/-- BSの具体的標準加群直極限は、適切な共通係数商上平坦。 -/
theorem deltaDivisionNormalizedModuleDirectLimit_moduleFlat :
    Module.Flat B (DeltaDivisionNormalizedModuleDirectLimit D d a u) := by
  let := deltaDivisionFiniteNormalizedLinearDirectedSystem D d a u
  let := fun N => deltaDivisionFiniteNormalized_moduleFlat D d a u N
  exact moduleDirectLimit_flat
    (fun N : ℕ => DeltaDivisionFiniteNormalizedQuotient D d a u N)
    (fun _ _ h => deltaDivisionFiniteNormalizedTowerLinearMap D d a u h)

/-- 構成済みの全段正規化環は、標準係数射によってA/(p,d,a_s)上平坦。 -/
theorem deltaDivisionFiniteNormalizedDirectLimit_moduleFlat :
    Module.Flat B (DeltaDivisionFiniteNormalizedDirectLimit D d a u) := by
  let := deltaDivisionNormalizedModuleDirectLimit_moduleFlat D d a u
  exact Module.Flat.of_linearEquiv (deltaDivisionNormalizedModuleDirectLimitEquiv D d a u).symm

/-- 実際のraw mod(p,d)全δ剰余商も、標準係数射によって適切な共通係数商上平坦。 -/
theorem deltaDivision_mod_pd_deltaClosure_moduleFlat
    (hpA : Function.Injective (fun b : A => (p : A) * b))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (hu : (u : A) = D.delta d) :
    letI := deltaDivision_mod_pd_deltaClosure_baseAlgebra D hpA hpL hg d a u hu
    Module.Flat B (RelativeFreeDeltaRing (R := A) σ ⧸
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))) := by
  let := deltaDivision_mod_pd_deltaClosure_baseAlgebra D hpA hpL hg d a u hu
  let := deltaDivisionFiniteNormalizedDirectLimit_moduleFlat D d a u
  exact Module.Flat.of_linearEquiv
    (deltaDivision_mod_pd_deltaClosure_directLimitAlgEquiv D hpA hpL hg d a u hu).toLinearEquiv

end SerrePositivity.BhattScholze
