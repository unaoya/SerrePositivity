module

public import SerrePositivity.CommutativeAlgebra.FrobeniusRootKernels
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # 両立するp冪根が生成するイデアル

著者公開版Theorem 7.4の根を持つ単項の場合に向けた代数部分。
perfectoid性・完備性を要求せず、一般の環で根イデアルが根基とは主張しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 指定された両立する根の全元が生成する具体的なイデアル。 -/
def compatibleRootIdeal (ρ : ℕ → R) : Ideal R := Ideal.span (Set.range ρ)

/-- 最初の元の主イデアルは根イデアルに含まれる。 -/
theorem span_root_zero_le_compatibleRootIdeal (ρ : ℕ → R) :
    Ideal.span {ρ 0} ≤ compatibleRootIdeal ρ :=
  (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_range_self)

/-- 根の主イデアルは単調増大する。既存の一段包含を再利用する。 -/
theorem compatibleRoot_principal_monotone (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) : Monotone (fun n ↦ Ideal.span {ρ n}) :=
  monotone_nat_of_le_succ (span_compatibleRoot_le_succ p (Fact.out : p.Prime).ne_zero ρ hρ)

/-- 根イデアルの各元は、ある一つの根の主イデアルに属する。 -/
theorem mem_compatibleRootIdeal_iff (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (x : R) :
    x ∈ compatibleRootIdeal ρ ↔ ∃ n, x ∈ Ideal.span {ρ n} := by
  rw [compatibleRootIdeal, Ideal.span_range_eq_iSup]
  exact Submodule.mem_iSup_of_directed _ (compatibleRoot_principal_monotone ρ hρ).directed_le

/-- 両立するp冪根のイデアルは冪等。B5の一般perfectoidイデアルとは区別する。 -/
theorem compatibleRootIdeal_mul_self (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    compatibleRootIdeal ρ * compatibleRootIdeal ρ = compatibleRootIdeal ρ := by
  apply le_antisymm Ideal.mul_le_left
  apply Ideal.span_le.mpr
  rintro _ ⟨n, rfl⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Fact.out : p.Prime).two_le
  rw [← hρ n, hk, pow_add, pow_two]
  exact Ideal.mul_mem_right _ (compatibleRootIdeal ρ * compatibleRootIdeal ρ)
    (Ideal.mul_mem_mul (Ideal.mem_span_range_self (x := n + 1))
      (Ideal.mem_span_range_self (x := n + 1)))

omit [Fact p.Prime] in
/-- 被約な終域への射が最初の元を消すなら、すべての根を消す。 -/
theorem compatibleRootIdeal_le_ker_of_root_zero {T : Type v} [CommRing T] [IsReduced T]
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (g : R →+* T) (hg : g (ρ 0) = 0) :
    compatibleRootIdeal ρ ≤ RingHom.ker g := by
  apply Ideal.span_le.mpr
  rintro _ ⟨n, rfl⟩
  change g (ρ n) = 0
  apply eq_zero_of_pow_eq_zero (n := p ^ n)
  have he := congrArg g (compatibleRoots_pow p ρ hρ 0 n)
  simpa only [zero_add, map_pow, hg] using he

/-- 根列を保存する射は、根イデアルを対応する根イデアルへ写す。 -/
theorem compatibleRootIdeal_map {T : Type v} [CommRing T] (ρ : ℕ → R) (g : R →+* T) :
    (compatibleRootIdeal ρ).map g = compatibleRootIdeal (fun n ↦ g (ρ n)) := by
  rw [compatibleRootIdeal, Ideal.map_span, compatibleRootIdeal, ← Set.range_comp]
  rfl

end SerrePositivity
