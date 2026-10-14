module

public import SerrePositivity.BhattScholze.DeltaDivisionNormalizedDirectLimitModule
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
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ g hg
  let G := fun N : ℕ => DeltaDivisionFiniteNormalizedQuotient D d a u N
  let F := fun n m (h : n ≤ m) => deltaDivisionFiniteNormalizedTowerLinearMap D d a u h
  let := deltaDivisionFiniteNormalizedLinearDirectedSystem D d a u
  let FP := fun n m h => (F n m h).rTensor P
  let FQ := fun n m h => (F n m h).rTensor Q
  have hc : ∀ n m h, (g.lTensor (G m)).comp (FP n m h) =
      (FQ n m h).comp (g.lTensor (G n)) := by
    intro n m h
    exact (LinearMap.lTensor_comp_rTensor (G n) (F n m h) g).trans
      (LinearMap.rTensor_comp_lTensor (G n) (F n m h) g).symm
  let t := Module.DirectLimit.map (f := FP) (f' := FQ) (fun n => g.lTensor (G n)) hc
  have ht : Function.Injective t := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨n, y, rfl⟩ := Module.DirectLimit.exists_of x
    dsimp only [t] at hx
    rw [Module.DirectLimit.map_apply_of] at hx
    obtain ⟨m, h, hz⟩ := Module.DirectLimit.of.zero_exact hx
    have hz' : g.lTensor (G m) (FP n m h y) = 0 := by
      change ((g.lTensor (G m)).comp (FP n m h)) y = 0
      rw [hc]
      exact hz
    let := deltaDivisionFiniteNormalized_moduleFlat D d a u m
    have hi : Function.Injective (g.lTensor (G m)) :=
      Module.Flat.lTensor_preserves_injective_linearMap g hg
    have hy : FP n m h y = 0 := hi (hz'.trans (map_zero _).symm)
    rw [← Module.DirectLimit.of_f (j := m) (hij := h), hy, map_zero]
  have hn : (TensorProduct.directLimitLeft F Q).toLinearMap.comp
      (g.lTensor (DeltaDivisionNormalizedModuleDirectLimit D d a u)) =
      t.comp (TensorProduct.directLimitLeft F P).toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
    change TensorProduct.directLimitLeft F Q
      ((g.lTensor (DeltaDivisionNormalizedModuleDirectLimit D d a u))
        (Module.DirectLimit.of B ℕ G F n z ⊗ₜ[B] y)) =
      t (TensorProduct.directLimitLeft F P (Module.DirectLimit.of B ℕ G F n z ⊗ₜ[B] y))
    rw [LinearMap.lTensor_tmul, TensorProduct.directLimitLeft_tmul_of,
      TensorProduct.directLimitLeft_tmul_of]
    dsimp only [t]
    rw [Module.DirectLimit.map_apply_of, LinearMap.lTensor_tmul]
  have hi : Function.Injective ((TensorProduct.directLimitLeft F Q).toLinearMap.comp
      (g.lTensor (DeltaDivisionNormalizedModuleDirectLimit D d a u))) := by
    rw [hn]
    exact ht.comp (TensorProduct.directLimitLeft F P).injective
  intro x y h
  exact hi (congrArg (TensorProduct.directLimitLeft F Q) h)

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
