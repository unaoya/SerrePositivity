module

public import SerrePositivity.CommutativeAlgebra.LocalizationInverse
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # 被約環上の有限自由加群への局所化同型 -/

@[expose] public noncomputable section
namespace SerrePositivity
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 被約環ではg冪ねじれの元をg自身が消す。 -/
theorem mul_eq_zero_of_pow_mul_eq_zero [IsReduced R] (g a : R)
    (h : ∃ n : ℕ, g ^ n * a = 0) : g * a = 0 := by
  obtain ⟨n, hn⟩ := h
  apply IsReduced.eq_zero
  refine ⟨n + 1, ?_⟩
  calc
    (g * a) ^ (n + 1) = (g ^ n * a) * (g * a ^ n) := by ring
    _ = 0 := by rw [hn, zero_mul]

/-- 自由加群の局所化で零になる元をg自身が消す。 -/
theorem smul_eq_zero_of_free_localized_zero [IsReduced R] (g : R) (r : ℕ)
    (y : Fin r → R)
    (hy : LocalizedModule.mkLinearMap (Submonoid.powers g) (Fin r → R) y = 0) :
    g • y = 0 := by
  obtain ⟨n, hn⟩ := exists_pow_smul_zero_of_localized_zero g y hy
  ext i
  exact mul_eq_zero_of_pow_mul_eq_zero g (y i) ⟨n, congrFun hn i⟩

/-- 有限自由加群への局所化同型の核・余核は一様なg冪で消える。
核の有限生成性も、RのNoether性も仮定しない。 -/
theorem exists_pow_ker_coker_annihilator [IsReduced R] [Module.Finite R M]
    (g : R) (r : ℕ) (f : M →ₗ[R] (Fin r → R))
    (hf : Function.Bijective (awayModuleMap g f)) :
    ∃ a b : ℕ, (∀ x : M, f x = 0 → g ^ a • x = 0) ∧
      (∀ y : (Fin r → R) ⧸ LinearMap.range f, g ^ b • y = 0) := by
  obtain ⟨k, ψ, _, hψ⟩ := exists_away_inverse g r f hf
  obtain ⟨b, hb⟩ := exists_uniform_pow_smul_coker_zero_of_away_surjective g f hf.surjective
  obtain ⟨c, hc⟩ := exists_uniform_pow_smul_coker_zero_of_away_surjective g ψ hψ.surjective
  refine ⟨c + 1, b, ?_, hb⟩
  intro x hx
  have hmem : g ^ c • x ∈ LinearMap.range ψ := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact (map_smul (LinearMap.range ψ).mkQ (g ^ c) x).trans (hc _)
  obtain ⟨y, hy⟩ := hmem
  have hcomp : f (ψ y) = 0 := by rw [hy, map_smul, hx, smul_zero]
  let ιF := LocalizedModule.mkLinearMap (Submonoid.powers g) (Fin r → R)
  have hzero : ιF y = 0 := by
    apply hψ.injective
    apply hf.injective
    simp only [map_zero, awayModuleMap, ιF, IsLocalizedModule.map_apply, hcomp]
  have hgy := smul_eq_zero_of_free_localized_zero g r y hzero
  calc
    g ^ (c + 1) • x = g • (g ^ c • x) := by rw [pow_succ', mul_smul]
    _ = ψ (g • y) := by rw [map_smul, hy]
    _ = 0 := by rw [hgy, map_zero]

end SerrePositivity
