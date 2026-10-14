module

public import SerrePositivity.CommutativeAlgebra.AdicStrictQuotient
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-! # mod aで正則な元による商のa進完備性

mod aの正則性からg倍写像の厳密なフィルトレーション比較を供給し、
商の完備性とaの非零因子性を確認する。環のNoether性は要求しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
variable (R : Type u) [CommRing R]

theorem dvd_of_mul_dvd_of_regular_mod (a g : R)
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g))
    (x : R) (hx : a ∣ g * x) : a ∣ x := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hg
  change Ideal.Quotient.mk (Ideal.span {a}) g * Ideal.Quotient.mk (Ideal.span {a}) x =
    Ideal.Quotient.mk (Ideal.span {a}) g * 0
  rw [← map_mul, mul_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hx)

theorem pow_dvd_of_mul_dvd_of_regular_mod (a g : R) (ha : IsSMulRegular R a)
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g))
    (n : ℕ) (x : R) (hx : a ^ n ∣ g * x) : a ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨y, hy⟩ := dvd_of_mul_dvd_of_regular_mod R a g hg x
      ((dvd_pow_self a (Nat.succ_ne_zero n)).trans hx)
    obtain ⟨z, hz⟩ := hx
    have hcancel : g * y = a ^ n * z := by
      apply ha
      change a * (g * y) = a * (a ^ n * z)
      calc
        _ = g * x := by rw [hy]; ring
        _ = a ^ (n + 1) * z := hz
        _ = _ := by rw [pow_succ]; ring
    obtain ⟨w, hw⟩ := ih y ⟨z, hcancel⟩
    exact ⟨w, by rw [hy, hw, pow_succ]; ring⟩

theorem isSMulRegular_quotient_span_of_regular_mod (a g : R) (ha : IsSMulRegular R a)
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g)) :
    IsSMulRegular (R ⧸ Ideal.span {g}) (Ideal.Quotient.mk (Ideal.span {g}) a) := by
  change IsSMulRegular (R ⧸ Ideal.span {g}) (algebraMap R (R ⧸ Ideal.span {g}) a)
  rw [isSMulRegular_algebraMap_iff]
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem (Ideal.span {g}) a).mpr
  intro x hx
  change a * x ∈ Ideal.span {g} at hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨z, hz⟩ := dvd_of_mul_dvd_of_regular_mod R a g hg y ⟨x, hy.symm⟩
  apply Ideal.mem_span_singleton.mpr
  refine ⟨z, ?_⟩
  apply ha
  change a * x = a * (g * z)
  rw [hy, hz]
  ring

theorem isAdicComplete_quotient_span_of_regular_mod (a g : R)
    [IsAdicComplete (Ideal.span {a}) R] (ha : IsSMulRegular R a)
    (hg : IsSMulRegular (R ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) g)) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a}) (R ⧸ Ideal.span {g}) := by
  let f := LinearMap.mulLeft R g
  have hbound : ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap f ((Ideal.span {a}) ^ (n + k) • (⊤ : Submodule R R)) ≤
        (Ideal.span {a}) ^ n • (⊤ : Submodule R R) := by
    refine ⟨0, fun n x hx ↦ ?_⟩
    simp only [Submodule.mem_comap, f, LinearMap.mulLeft_apply, Nat.add_zero,
      Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢
    exact pow_dvd_of_mul_dvd_of_regular_mod R a g ha hg n x hx
  have hrange : f.range = (Ideal.span {g} : Submodule R R) := by
    ext x
    simp only [LinearMap.mem_range, f, LinearMap.mulLeft_apply, Ideal.mem_span_singleton, dvd_def]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩⟩
  let : IsAdicComplete (Ideal.span {a}) (R ⧸ Ideal.span {g}) := by
    rw [← hrange]
    exact isAdicComplete_quotient_range_of_uniform_filtration_bound (Ideal.span {a}) f hbound
  have hmap : (Ideal.span {a}).map (algebraMap R (R ⧸ Ideal.span {g})) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) a} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance

end SerrePositivity
