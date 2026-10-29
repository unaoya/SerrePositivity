module

public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed
public import SerrePositivity.CommutativeAlgebra.PerfectoidTorsionFrobenius
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity

/-! # Complete radical quotients of absolutely integrally closed perfectoid rings

Actual compatible roots of every element of a radical ideal stay in that ideal.
The existing perfectoid root-family completion then supplies the perfectoid quotient.
In particular this applies to the annihilator of any original scalar.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open BhattScholze
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]

/-- Every complete radical quotient of an absolutely integrally closed perfectoid
ring is perfectoid; no finite generation or regularity is needed. -/
theorem aicPerfectoid_quotient_of_radical_and_complete
    (hR : IsIntegralPerfectoid R p) (hAIC : IsAbsolutelyIntegrallyClosed R)
    (J : Ideal R) (hJ : J.IsRadical)
    [IsAdicComplete (Ideal.span {(p : R ⧸ J)}) (R ⧸ J)] :
    IsIntegralPerfectoid (R ⧸ J) p := by
  classical
  choose ρ hρ0 hρ using fun s : J =>
    hAIC.exists_compatible_pow_roots (Fact.out : p.Prime).pos (s : R)
  have hmem (s : J) (n : ℕ) : ρ s n ∈ J := by
    apply hJ
    refine ⟨p ^ n, ?_⟩
    have hp := compatibleRoots_pow p (ρ s) (hρ s) 0 n
    have he : ρ s n ^ (p ^ n) = (s : R) := by
      simpa only [Nat.zero_add, hρ0] using hp
    rw [he]
    exact s.property
  have hK : SerrePositivity.compatibleRootFamilyIdeal ρ = J := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨s, n⟩, rfl⟩
      exact hmem s n
    · exact (compatibleRootFamilyZeroIdeal_eq_of_roots_on_ideal J ρ hρ0).ge.trans
        (compatibleRootFamilyZeroIdeal_le ρ)
  have hT := compatibleRootFamilyCompletion_isIntegralPerfectoid hR ρ hρ
  change IsIntegralPerfectoid
    (AdicCompletion (Ideal.span {(p : R ⧸ SerrePositivity.compatibleRootFamilyIdeal ρ)})
      (R ⧸ SerrePositivity.compatibleRootFamilyIdeal ρ)) p at hT
  rw [hK] at hT
  let e : (R ⧸ J) ≃+* AdicCompletion (Ideal.span {(p : R ⧸ J)}) (R ⧸ J) :=
    RingEquiv.ofBijective (algebraMap _ _) (by
      change Function.Bijective (AdicCompletion.of _ _)
      exact AdicCompletion.of_bijective _ _)
  exact isIntegralPerfectoid_of_ringEquiv p e.symm hT

omit [Fact p.Prime] in
/-- The quotient by a scalar annihilator is complete over its own p-adic ideal. -/
theorem annihilatorPrincipalQuotient_isAdicComplete (g : R)
    [IsAdicComplete (Ideal.span {(p : R)}) R] :
    IsAdicComplete (Ideal.span {(p : R ⧸ (Ideal.span {g}).annihilator)})
      (R ⧸ (Ideal.span {g}).annihilator) := by
  have hker : (Ideal.span {g}).annihilator = LinearMap.ker (LinearMap.mulLeft R g) := by
    ext x
    rw [Submodule.mem_annihilator_span_singleton, LinearMap.mem_ker]
    change x * g = 0 ↔ g * x = 0
    rw [mul_comm]
  let : IsAdicComplete (Ideal.span {(p : R)}) (R ⧸ (Ideal.span {g}).annihilator) := by
    rw [hker]
    exact isAdicComplete_quotient_ker (Ideal.span {(p : R)}) (LinearMap.mulLeft R g)
  have hmap : (Ideal.span {(p : R)}).map
      (algebraMap R (R ⧸ (Ideal.span {g}).annihilator)) =
      Ideal.span {(p : R ⧸ (Ideal.span {g}).annihilator)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance

/-- A scalar annihilator in any reduced ring is radical. -/
theorem annihilatorPrincipal_isRadical_of_reduced [IsReduced R] (g : R) :
    (Ideal.span {g}).annihilator.IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have he : g * x ^ n = 0 := by
    have hh := (Submodule.mem_annihilator_span_singleton g (x ^ n)).mp hn
    simpa only [smul_eq_mul, mul_comm] using hh
  apply (Submodule.mem_annihilator_span_singleton g x).mpr
  change x * g = 0
  rw [mul_comm]
  apply IsReduced.eq_zero
  refine ⟨n + 1, ?_⟩
  calc
    (g * x) ^ (n + 1) = g ^ n * (g * x ^ n) * x := by
      rw [mul_pow, pow_succ, pow_succ]
      ring
    _ = 0 := by rw [he]; simp

/-- The actual annihilator quotient of an absolutely integrally closed perfectoid
ring is perfectoid for every scalar, including zero and zero divisors. -/
theorem aicPerfectoid_annihilatorPrincipalQuotient
    (hR : IsIntegralPerfectoid R p) (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R) :
    IsIntegralPerfectoid (R ⧸ (Ideal.span {g}).annihilator) p := by
  let := hR.isReduced R p
  let := hR.isAdicComplete R p
  let := annihilatorPrincipalQuotient_isAdicComplete R p g
  exact aicPerfectoid_quotient_of_radical_and_complete R p hR hAIC _
    (annihilatorPrincipal_isRadical_of_reduced R g)

end SerrePositivity
