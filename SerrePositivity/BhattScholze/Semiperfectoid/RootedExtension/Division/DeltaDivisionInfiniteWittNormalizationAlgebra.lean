module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionInfiniteWittNormalization

/-! # 実際のraw全δ剰余商の共通係数商上の代数表示 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun b : A => (p : A) * b))
variable (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
  (p : RelativeFreeDeltaRing (R := A) σ) * f))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)

/-- 適切な共通係数商から実際のraw mod(p,d)全δ商への具体的係数射。 -/
def deltaDivision_mod_pd_deltaClosure_baseMap :
    A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a →+*
      (RelativeFreeDeltaRing (R := A) σ ⧸
        (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
          (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))) :=
  (deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu).symm.toRingHom.comp
    (deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u)

/-- この係数射は元の基底係数の標準商像に一致する。 -/
theorem deltaDivision_mod_pd_deltaClosure_baseMap_mk (b : A) :
    deltaDivision_mod_pd_deltaClosure_baseMap D hpA hpL hg d a u hu (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (MvPolynomial.C b) := by
  apply (deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu).injective
  change (deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu)
    ((deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu).symm _) = _
  rw [RingEquiv.apply_symm_apply, deltaDivision_mod_pd_deltaClosure_directLimitEquiv_C]

/-- 標準係数射による、適切な共通係数商上の実際のraw全δ剰余商の代数構造。 -/
@[instance_reducible] def deltaDivision_mod_pd_deltaClosure_baseAlgebra :
    Algebra (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (RelativeFreeDeltaRing (R := A) σ ⧸
        (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
          (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))) :=
  (deltaDivision_mod_pd_deltaClosure_baseMap D hpA hpL hg d a u hu).toAlgebra

/-- 実際のraw全δ剰余商と全段環の比較は、標準共通係数射に関する代数同型。 -/
def deltaDivision_mod_pd_deltaClosure_directLimitAlgEquiv :
    letI := deltaDivision_mod_pd_deltaClosure_baseAlgebra D hpA hpL hg d a u hu
    letI := deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
    (RelativeFreeDeltaRing (R := A) σ ⧸
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))) ≃ₐ[
      A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a]
      DeltaDivisionFiniteNormalizedDirectLimit D d a u := by
  letI := deltaDivision_mod_pd_deltaClosure_baseAlgebra D hpA hpL hg d a u hu
  letI := deltaDivisionFiniteNormalizedDirectLimitBaseAlgebra D d a u
  apply AlgEquiv.ofRingEquiv
    (f := deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu)
  intro b
  exact (deltaDivision_mod_pd_deltaClosure_directLimitEquiv
    D hpA hpL hg d a u hu).apply_symm_apply _

/-- 適切な共通係数商から実際のraw mod(p,d)全δ商への係数射は単射。 -/
theorem deltaDivision_mod_pd_deltaClosure_baseMap_injective :
    Function.Injective (deltaDivision_mod_pd_deltaClosure_baseMap D hpA hpL hg d a u hu) :=
  (deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu).symm.injective.comp
    (deltaDivisionFiniteNormalizedDirectLimitBaseMap_injective D d a u)

end SerrePositivity.BhattScholze
