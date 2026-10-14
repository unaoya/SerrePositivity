module

public import SerrePositivity.BhattScholze.DeltaDivisionNormalizedTensorTransition

/-! # BSの具体的全段環とraw全δ商の共通係数商上の忠実平坦性 -/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ)
attribute [local instance] deltaDivisionFiniteNormalizedBaseAlgebra
  deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra
local notation "R₀" => (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)

/-- 各有限段テンソルから具体的テンソル直極限への標準射は単射。 -/
theorem deltaDivisionNormalizedTensorDirectLimitOf_injective
    (N : Type w) [AddCommGroup N] [Module R₀ N] (n : ℕ) :
    Function.Injective (Module.DirectLimit.of R₀ ℕ
      (fun i => DeltaDivisionFiniteNormalizedQuotient D d a u i ⊗[R₀] N)
      (fun _ _ h => (deltaDivisionFiniteNormalizedTowerLinearMap D d a u h).rTensor N) n) := by
  let := deltaDivisionFiniteNormalizedLinearDirectedSystem D d a u
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨m, h, hz⟩ := Module.DirectLimit.of.zero_exact hx
  exact deltaDivisionFiniteNormalizedTower_rTensor_injective D d a u h N
    (hz.trans (map_zero _).symm)

/-- 全段正規化環は標準係数射によってA/(p,d,a_s)上忠実平坦。零係数商も含む。 -/
theorem deltaDivisionFiniteNormalizedDirectLimit_moduleFaithfullyFlat :
    Module.FaithfullyFlat R₀ (DeltaDivisionFiniteNormalizedDirectLimit D d a u) := by
  rw [Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality]
  refine ⟨deltaDivisionFiniteNormalizedDirectLimit_moduleFlat D d a u, ?_⟩
  intro N _ _ hN
  let := hN
  let := deltaDivisionFiniteNormalized_moduleFaithfullyFlat D d a u 0
  let F := fun i j (h : i ≤ j) => deltaDivisionFiniteNormalizedTowerLinearMap D d a u h
  let e := TensorProduct.congr (deltaDivisionNormalizedModuleDirectLimitEquiv D d a u)
    (LinearEquiv.refl R₀ N)
  let l := TensorProduct.directLimitLeft F N
  have hi₁ : Function.Injective
      (TensorProduct.mk R₀ (DeltaDivisionFiniteNormalizedQuotient D d a u 0) N 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := R₀) (B := DeltaDivisionFiniteNormalizedQuotient D d a u 0) N
  have hi₂ := deltaDivisionNormalizedTensorDirectLimitOf_injective D d a u N 0
  have hi := e.injective.comp (l.symm.injective.comp (hi₂.comp hi₁))
  exact hi.subsingleton

/-- 実際のraw mod(p,d)全δ商も標準係数射によって適切な共通係数商上忠実平坦。 -/
theorem deltaDivision_mod_pd_deltaClosure_moduleFaithfullyFlat
    (hpA : Function.Injective (fun b : A => (p : A) * b))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (hu : (u : A) = D.delta d) :
    letI := deltaDivision_mod_pd_deltaClosure_baseAlgebra D hpA hpL hg d a u hu
    Module.FaithfullyFlat R₀ (RelativeFreeDeltaRing (R := A) σ ⧸
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))) := by
  let := deltaDivision_mod_pd_deltaClosure_baseAlgebra D hpA hpL hg d a u hu
  let := deltaDivisionFiniteNormalizedDirectLimit_moduleFaithfullyFlat D d a u
  exact Module.FaithfullyFlat.of_linearEquiv R₀ _
    (deltaDivision_mod_pd_deltaClosure_directLimitAlgEquiv D hpA hpL hg d a u hu).toLinearEquiv

end SerrePositivity.BhattScholze
