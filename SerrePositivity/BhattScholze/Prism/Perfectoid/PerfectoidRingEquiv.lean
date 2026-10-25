module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.FontaineNaturality
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.AdicCompletion.Topology

/-! # 完全prismの商同型に沿う既存perfectoid述語の移送 -/

@[expose] public noncomputable section
namespace SerrePositivity.BhattScholze
variable {R S : Type*} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]

private def modPEquiv (e : R ≃+* S) : ModP R p ≃+* ModP S p :=
  Ideal.quotientEquiv _ _ e (by simp only [Ideal.map_span, Set.image_singleton, map_natCast])

omit [Fact p.Prime] in
private theorem modPEquiv_apply (e : R ≃+* S) (x : ModP R p) :
    modPEquiv p e x = modPMap p e.toRingHom x := rfl

/-- BSの商比較に使う環同型に沿って、既存の整perfectoid性を移す。 -/
theorem isIntegralPerfectoid_of_ringEquiv (e : R ≃+* S) (hR : IsIntegralPerfectoid R p) :
    IsIntegralPerfectoid S p := by
  rcases hR with hs | ⟨hp, hc, ⟨π, a, ha⟩, hF, hker⟩
  · exact Or.inl (Function.Injective.subsingleton e.symm.injective)
  · have hpS : ¬ IsUnit (p : S) := by
      intro hu
      apply hp
      simpa only [map_natCast] using hu.map e.symm.toRingHom
    have hcS : IsAdicComplete (Ideal.span {(p : S)}) S := by
      have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {(p : R)}) e).mpr hc
      simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using h
    let := hc
    let := hcS
    let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    let : Fact (¬ IsUnit (p : S)) := ⟨hpS⟩
    let em := modPEquiv p e
    let t := Perfection.map p (modPMap p e.toRingHom)
    have ht : Function.Bijective t := by
      constructor
      · intro x y h
        apply Perfection.ext
        intro n
        apply em.injective
        have hh := congrArg (Perfection.coeff (ModP S p) p n) h
        change modPMap p e.toRingHom (Perfection.coeff (ModP R p) p n x) =
          modPMap p e.toRingHom (Perfection.coeff (ModP R p) p n y) at hh
        exact hh
      · intro y
        refine ⟨Perfection.map p em.symm.toRingHom y, ?_⟩
        apply Perfection.ext
        intro n
        change em (em.symm (Perfection.coeff (ModP S p) p n y)) = _
        exact em.apply_symm_apply _
    let ψ : WittVector p (PreTilt R p) →+* WittVector p (PreTilt S p) := WittVector.map t
    have hψ : Function.Surjective ψ := WittVector.map_surjective _ ht.2
    refine Or.inr ⟨hpS, hcS, ⟨e π, Units.map e.toMonoidHom a, ?_⟩, ?_, ?_⟩
    · change (p : S) = e (a : R) * (e π) ^ p
      simpa only [map_natCast, map_mul, map_pow] using congrArg e ha
    · intro y
      obtain ⟨x, hx⟩ := hF (em.symm y)
      refine ⟨em x, ?_⟩
      change (em x) ^ p = y
      change x ^ p = em.symm y at hx
      rw [← map_pow, hx, em.apply_symm_apply]
    · have he : (RingHom.ker (WittVector.fontaineTheta S p)).comap ψ =
          RingHom.ker (WittVector.fontaineTheta R p) := by
        ext x
        change WittVector.fontaineTheta S p (ψ x) = 0 ↔
          WittVector.fontaineTheta R p x = 0
        have hn := RingHom.congr_fun (fontaineTheta_natural p e.toRingHom) x
        change WittVector.fontaineTheta S p (ψ x) = e (WittVector.fontaineTheta R p x) at hn
        rw [hn, map_eq_zero_iff e e.injective]
      have hm := hker.map_ringHom ψ
      rw [← he, Ideal.map_comap_of_surjective ψ hψ] at hm
      exact hm

end SerrePositivity.BhattScholze
