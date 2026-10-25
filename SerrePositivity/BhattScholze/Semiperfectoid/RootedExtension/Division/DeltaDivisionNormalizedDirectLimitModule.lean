module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionInfiniteWittNormalizationAlgebra
public import Mathlib.Algebra.Colimit.Module

/-! # 全段正規化環と具体的加群直極限の比較 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ)
attribute [local instance] deltaDivisionFiniteNormalizedBaseAlgebra
  deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra

/-- 共通係数商上の具体的標準線形塔による、既存の加群直極限。 -/
abbrev DeltaDivisionNormalizedModuleDirectLimit :=
  Module.DirectLimit (fun N : ℕ => DeltaDivisionFiniteNormalizedQuotient D d a u N)
    (fun _ _ h => deltaDivisionFiniteNormalizedTowerLinearMap D d a u h)

/-- 各段の標準線形射を既存加群直極限の普遍性で全段環へまとめた射。 -/
def deltaDivisionNormalizedModuleDirectLimitMap :
    DeltaDivisionNormalizedModuleDirectLimit D d a u →ₗ[
      A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a]
      DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  Module.DirectLimit.lift (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a) ℕ _ _
    (fun N => deltaDivisionFiniteNormalizedDirectLimitOfLinearMap D d a u N)
    (fun _ _ h x => deltaDivisionFiniteNormalizedDirectLimitOf_compatible D d a u h x)

/-- 加群直極限からの射は、各段の標準像を構成済み全段環の標準像へ送る。 -/
theorem deltaDivisionNormalizedModuleDirectLimitMap_of (N : ℕ)
    (x : DeltaDivisionFiniteNormalizedQuotient D d a u N) :
    deltaDivisionNormalizedModuleDirectLimitMap D d a u
      (Module.DirectLimit.of (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a) ℕ _
        (fun _ _ h => deltaDivisionFiniteNormalizedTowerLinearMap D d a u h) N x) =
      deltaDivisionFiniteNormalizedDirectLimitOf D d a u N x := by
  rw [deltaDivisionNormalizedModuleDirectLimitMap, Module.DirectLimit.lift_of]
  rfl

/-- 構成済み全段環は、共通係数商上の具体的加群直極限と線形同型。 -/
def deltaDivisionNormalizedModuleDirectLimitEquiv :
    DeltaDivisionNormalizedModuleDirectLimit D d a u ≃ₗ[
      A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a]
      DeltaDivisionFiniteNormalizedDirectLimit D d a u := by
  let := deltaDivisionFiniteNormalizedLinearDirectedSystem D d a u
  apply LinearEquiv.ofBijective (deltaDivisionNormalizedModuleDirectLimitMap D d a u)
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨N, y, rfl⟩ := Module.DirectLimit.exists_of x
    rw [deltaDivisionNormalizedModuleDirectLimitMap_of] at hx
    have hy : y = 0 := deltaDivisionFiniteNormalizedDirectLimitOf_injective D d a u N
      (hx.trans (map_zero (deltaDivisionFiniteNormalizedDirectLimitOf D d a u N)).symm)
    rw [hy, map_zero]
  · intro y
    obtain ⟨N, x, hx⟩ := deltaDivisionFiniteNormalizedDirectLimit_exists_stage D d a u y
    exact ⟨Module.DirectLimit.of (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a) ℕ _
      (fun _ _ h => deltaDivisionFiniteNormalizedTowerLinearMap D d a u h) N x,
      (deltaDivisionNormalizedModuleDirectLimitMap_of D d a u N x).trans hx⟩

/-- 線形同型も各段の標準像に両立する。 -/
theorem deltaDivisionNormalizedModuleDirectLimitEquiv_of (N : ℕ)
    (x : DeltaDivisionFiniteNormalizedQuotient D d a u N) :
    deltaDivisionNormalizedModuleDirectLimitEquiv D d a u
      (Module.DirectLimit.of (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a) ℕ _
        (fun _ _ h => deltaDivisionFiniteNormalizedTowerLinearMap D d a u h) N x) =
      deltaDivisionFiniteNormalizedDirectLimitOf D d a u N x :=
  deltaDivisionNormalizedModuleDirectLimitMap_of D d a u N x

end SerrePositivity.BhattScholze
