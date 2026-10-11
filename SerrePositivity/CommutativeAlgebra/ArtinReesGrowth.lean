module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuelBasic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Artin–Rees and growth after quotienting by a regular element

For a finite module, Artin–Rees bounds the inverse image of `IⁿM` under
multiplication by a regular element. The resulting length inequality compares
the Samuel function of `M/xM` with a bounded difference of that of `M`.
-/

@[expose] public section

universe u

open scoped Pointwise

namespace SerrePositivity.HilbertSamuel

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- The quotient by a scalar gives a short exact sequence in each filtration
degree; the first term is the quotient by the inverse image under multiplication. -/
lemma samuelFunction_quotSMulTop_eq (I : Ideal R) (x : R) (n : ℕ) :
    samuelFunction R I M n =
      Module.length R (M ⧸ (I ^ n • ⊤ : Submodule R M).comap
        (LinearMap.lsmul R M x)) + samuelFunction R I (QuotSMulTop x M) n := by
  let N : Submodule R M := I ^ n • ⊤
  let f : M →ₗ[R] M := LinearMap.lsmul R M x
  let P : Submodule R M := N.comap f
  let T : Submodule R M := x • ⊤
  let q : M →ₗ[R] QuotSMulTop x M := T.mkQ
  let U : Submodule R (QuotSMulTop x M) := I ^ n • ⊤
  let a : M ⧸ P →ₗ[R] M ⧸ N := P.mapQ N f le_rfl
  let b : M ⧸ N →ₗ[R] QuotSMulTop x M ⧸ U :=
    N.mapQ U q (Submodule.smul_top_le_comap_smul_top (I ^ n) q)
  have ha : Function.Injective a := by
    apply LinearMap.ker_eq_bot.mp
    change LinearMap.ker (P.mapQ N f le_rfl) = ⊥
    rw [Submodule.ker_mapQ, Submodule.mkQ_map_self]
  have hb : Function.Surjective b := by
    intro z
    obtain ⟨z, rfl⟩ := U.mkQ_surjective z
    obtain ⟨z, rfl⟩ := T.mkQ_surjective z
    exact ⟨N.mkQ z, rfl⟩
  have hf : LinearMap.range f = T := by
    change LinearMap.range (LinearMap.lsmul R M x) = x • ⊤
    rw [Submodule.pointwise_smul_def, Submodule.map_top]
    rfl
  have hab : Function.Exact a b := by
    apply LinearMap.exact_iff.mpr
    symm
    change LinearMap.range (P.mapQ N f le_rfl) = LinearMap.ker
      (N.mapQ U q (Submodule.smul_top_le_comap_smul_top (I ^ n) q))
    rw [Submodule.range_mapQ, Submodule.ker_mapQ, hf,
      Submodule.comap_smul_top_of_surjective (I ^ n) q (T.mkQ_surjective),
      Submodule.map_sup]
    change T.map N.mkQ = N.map N.mkQ ⊔ (LinearMap.ker q).map N.mkQ
    rw [show LinearMap.ker q = T from Submodule.ker_mkQ T,
      Submodule.mkQ_map_self, bot_sup_eq]
  exact Module.length_eq_add_of_exact a b ha hb hab

/-- Artin–Rees bounds the inverse image of powers by multiplication by a
regular element, with a strictly positive shift. -/
lemma exists_comap_pow_smul_top_le [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (x : R) (hx : IsSMulRegular M x) :
    ∃ c : ℕ, 0 < c ∧ ∀ n ≥ c,
      (I ^ n • ⊤ : Submodule R M).comap (LinearMap.lsmul R M x) ≤
        I ^ (n - c) • ⊤ := by
  let f : M →ₗ[R] M := LinearMap.lsmul R M x
  have hf : Function.Injective f := hx
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨k + 1, by omega, fun n hn => ?_⟩
  have hkn : k ≤ n := by omega
  have he : (I ^ n • ⊤ : Submodule R M).comap f ≤ I ^ (n - k) • ⊤ := by
    apply (Submodule.map_le_map_iff_of_injective hf _ _).mp
    rw [Submodule.map_comap_eq, inf_comm, hk n hkn,
      Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right
  exact he.trans (Submodule.smul_mono
    (Ideal.pow_le_pow_right (by omega : n - (k + 1) ≤ n - k)) le_rfl)

/-- Killing a regular element lowers the Samuel growth by one bounded
difference. No subtraction, and no finite-length hypotheses, are needed. -/
theorem exists_samuelFunction_quotSMulTop_add_le [IsNoetherianRing R]
    [Module.Finite R M] (I : Ideal R) (x : R) (hx : IsSMulRegular M x) :
    ∃ c : ℕ, 0 < c ∧ ∀ n ≥ c,
      samuelFunction R I (QuotSMulTop x M) n + samuelFunction R I M (n - c) ≤
        samuelFunction R I M n := by
  obtain ⟨c, hc, h⟩ := exists_comap_pow_smul_top_le I x hx
  refine ⟨c, hc, fun n hn => ?_⟩
  have hl := Module.length_le_of_surjective (Submodule.factor (h n hn))
    (Submodule.factor_surjective (h n hn))
  calc
    _ ≤ samuelFunction R I (QuotSMulTop x M) n +
        Module.length R (M ⧸ (I ^ n • ⊤ : Submodule R M).comap
          (LinearMap.lsmul R M x)) := add_le_add_right hl _
    _ = samuelFunction R I M n := by
      rw [add_comm]
      exact (samuelFunction_quotSMulTop_eq (M := M) I x n).symm

end SerrePositivity.HilbertSamuel
