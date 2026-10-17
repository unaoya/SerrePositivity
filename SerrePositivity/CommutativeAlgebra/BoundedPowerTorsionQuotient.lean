module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Regular.SMul

/-! # 有界な冪 torsion を除いた商でのスカラーの正則性

全ての a 冪 torsion が a^N で消えるとき、a^N の核で割ると a は正則に作用する。
Noether 性、有限性、元環の a 正則性を要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 元の共通 torsion 指数の核で割った商では、a が正則に作用する。 -/
theorem isSMulRegular_quotient_pow_kernel (a : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0) :
    IsSMulRegular (M ⧸ (a ^ N • (LinearMap.id : M →ₗ[R] M)).ker) a := by
  let T := (a ^ N • (LinearMap.id : M →ₗ[R] M)).ker
  change Function.Injective (a • (LinearMap.id : (M ⧸ T) →ₗ[R] (M ⧸ T)))
  apply (injective_iff_map_eq_zero _).mpr
  intro y hy
  obtain ⟨x, rfl⟩ := T.mkQ_surjective y
  apply (Submodule.Quotient.mk_eq_zero T).mpr
  have hx : a • x ∈ T := by
    apply (Submodule.Quotient.mk_eq_zero T).mp
    change T.mkQ (a • x) = 0
    rw [map_smul]
    exact hy
  have hx' : a ^ (N + 1) • x = 0 := by
    change a ^ N • (a • x) = 0 at hx
    simpa only [pow_succ, mul_smul] using hx
  exact h (N + 1) x hx'

/-- 有界な a 冪 torsion は、a^N で消える実核と a 正則な実商へ分解できる。 -/
theorem bounded_power_torsion_decomposition (a : R)
    (h : ∃ N : ℕ, ∀ n : ℕ, ∀ x : M, a ^ n • x = 0 → a ^ N • x = 0) :
    ∃ N : ℕ,
      (∀ x : (a ^ N • (LinearMap.id : M →ₗ[R] M)).ker, a ^ N • x = 0) ∧
      IsSMulRegular (M ⧸ (a ^ N • (LinearMap.id : M →ₗ[R] M)).ker) a := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun x => Subtype.ext x.property,
    isSMulRegular_quotient_pow_kernel a N hN⟩

end SerrePositivity
