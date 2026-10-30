module

public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Dimension
public import SerrePositivity.CommutativeAlgebra.Support.Closed
public import SerrePositivity.CommutativeAlgebra.SupportHeight

/-! # Natural height bounds on finite module supports -/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open Adams
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Nonzero module support dimensions are recovered from their natural values. -/
lemma natCast_dimToNat_supportDim (M : Type u) [AddCommGroup M] [Module R M]
    [Nontrivial M] :
    (dimToNat (Module.supportDim R M) : WithBot ℕ∞) = Module.supportDim R M := by
  obtain ⟨p, _, _, hp⟩ := exists_minimumHeight_support_prime (R := R) M
  have := finiteRingKrullDim_primeQuotient p
  rw [hp]
  exact natCast_dimToNat_ringKrullDim (R ⧸ p.asIdeal)

/-- The numerical support codimension and dimension add to the ring dimension. -/
lemma regular_supportCodimension_toNat_add_dimToNat (M : Type u)
    [AddCommGroup M] [Module R M] [Nontrivial M] :
    (supportCodimension R M).toNat + dimToNat (Module.supportDim R M) =
      dimToNat (ringKrullDim R) := by
  obtain ⟨p, _, hc, hd⟩ := exists_minimumHeight_support_prime (R := R) M
  rw [hc, hd]
  exact regular_primeHeight_toNat_add_quotientDimToNat p

/-- The least support height bounds every point of the closed module support. -/
lemma heightAtLeast_finiteModuleClosedSupport (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    HeightAtLeast (finiteModuleClosedSupport R M) (supportCodimension R M).toNat := by
  obtain ⟨q, _, hc, _⟩ := exists_minimumHeight_support_prime (R := R) M
  intro p hp
  have hp' : p ∈ Module.support R M := by
    rw [← finiteModuleClosedSupport_coe R M]
    exact hp
  rw [hc, natCast_primeHeight_toNat q]
  rw [← hc]
  exact supportCodimension_le_height hp'

omit [IsRegularLocalRing R] in
/-- Empty module support admits any height lower bound. -/
lemma heightAtLeast_finiteModuleClosedSupport_of_subsingleton (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Subsingleton M] (c : ℕ) :
    HeightAtLeast (finiteModuleClosedSupport R M) c := by
  intro p hp
  have hp' : p ∈ Module.support R M := by
    rw [← finiteModuleClosedSupport_coe R M]
    exact hp
  simp only [Module.support_eq_empty, Set.mem_empty_iff_false] at hp'

/-- Strict dimension bounds yield support height bounds, including empty supports. -/
lemma exists_supportHeight_sum_gt (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R) :
    ∃ cM cN : ℕ, HeightAtLeast (finiteModuleClosedSupport R M) cM ∧
      HeightAtLeast (finiteModuleClosedSupport R N) cN ∧
      dimToNat (ringKrullDim R) < cM + cN := by
  classical
  cases subsingleton_or_nontrivial M with
  | inl hM =>
      let : Subsingleton M := hM
      refine ⟨dimToNat (ringKrullDim R) + 1, 0,
        heightAtLeast_finiteModuleClosedSupport_of_subsingleton M _,
        heightAtLeast_zero _, ?_⟩
      omega
  | inr hM =>
      let : Nontrivial M := hM
      cases subsingleton_or_nontrivial N with
      | inl hN =>
          let : Subsingleton N := hN
          refine ⟨0, dimToNat (ringKrullDim R) + 1, heightAtLeast_zero _,
            heightAtLeast_finiteModuleClosedSupport_of_subsingleton N _, ?_⟩
          omega
      | inr hN =>
          let : Nontrivial N := hN
          refine ⟨(supportCodimension R M).toNat, (supportCodimension R N).toNat,
            heightAtLeast_finiteModuleClosedSupport M,
            heightAtLeast_finiteModuleClosedSupport N, ?_⟩
          have hM' := regular_supportCodimension_toNat_add_dimToNat (R := R) M
          have hN' := regular_supportCodimension_toNat_add_dimToNat (R := R) N
          rw [← natCast_dimToNat_supportDim M, ← natCast_dimToNat_supportDim N,
            ← natCast_dimToNat_ringKrullDim R] at hdim
          have hd : dimToNat (Module.supportDim R M) + dimToNat (Module.supportDim R N) <
              dimToNat (ringKrullDim R) := by exact_mod_cast hdim
          omega

end SerrePositivity
