module

public import SerrePositivity.BhattScholze.CompatibleRootIdealFlat
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # B4-5：根イデアルのテンソルと終域への単射

BS17 Lemma 3.16の根イデアルの計算。正のTorの一般消滅や完備性は別工程。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 根列の各元を、その生成するイデアルの元として扱う。 -/
def compatibleRootIdealElement (ρ : ℕ → R) (n : ℕ) : compatibleRootIdeal ρ :=
  ⟨ρ n, Ideal.mem_span_range_self⟩

/-- 根イデアルのテンソルの任意の元は、一つの根を第1成分に持つ。 -/
theorem compatibleRootIdeal_tensor_singleStage
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    {C : Type u} [CommRing C] [Algebra R C] (z : compatibleRootIdeal ρ ⊗[R] C) :
    ∃ n : ℕ, ∃ c : C, z = compatibleRootIdealElement ρ n ⊗ₜ[R] c := by
  refine TensorProduct.inductionOn
    (motive := fun z ↦ ∃ n : ℕ, ∃ c : C, z = compatibleRootIdealElement ρ n ⊗ₜ[R] c)
    z (fun x c ↦ ?_) (fun x y hx hy ↦ ?_)
  · obtain ⟨n, hn⟩ := (mem_compatibleRootIdeal_iff ρ hρ x).mp x.property
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hn
    have he : x = b • compatibleRootIdealElement ρ n := by
      apply Subtype.ext
      change (x : R) = b * ρ n
      rw [hb, mul_comm]
    refine ⟨n, b • c, ?_⟩
    rw [he, TensorProduct.smul_tmul]
  · obtain ⟨n, c, hx⟩ := hx
    obtain ⟨m, d, hy⟩ := hy
    let L := max n m
    have hn : ρ n ∈ Ideal.span {ρ L} := compatibleRoot_principal_monotone ρ hρ
      (Nat.le_max_left n m) (Ideal.mem_span_singleton_self _)
    have hm : ρ m ∈ Ideal.span {ρ L} := compatibleRoot_principal_monotone ρ hρ
      (Nat.le_max_right n m) (Ideal.mem_span_singleton_self _)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hn
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hm
    have hna : compatibleRootIdealElement ρ n = a • compatibleRootIdealElement ρ L := by
      apply Subtype.ext
      change ρ n = a * ρ L
      rw [ha, mul_comm]
    have hmb : compatibleRootIdealElement ρ m = b • compatibleRootIdealElement ρ L := by
      apply Subtype.ext
      change ρ m = b * ρ L
      rw [hb, mul_comm]
    refine ⟨L, a • c + b • d, ?_⟩
    rw [hx, hy, hna, hmb, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      TensorProduct.tmul_add]

/-- 根イデアルのテンソルから終域への、包含と乗法により定まる線形射。 -/
def compatibleRootIdealTensorMap (ρ : ℕ → R) (C : Type u) [CommRing C] [Algebra R C] :
    compatibleRootIdeal ρ ⊗[R] C →ₗ[R] C :=
  (TensorProduct.lid R C).toLinearMap ∘ₗ ((compatibleRootIdeal ρ).subtype.rTensor C)

/-- テンソル射の純粋テンソル上の式。 -/
@[simp] theorem compatibleRootIdealTensorMap_tmul
    (ρ : ℕ → R) (C : Type u) [CommRing C] [Algebra R C]
    (x : compatibleRootIdeal ρ) (c : C) :
    compatibleRootIdealTensorMap ρ C (x ⊗ₜ[R] c) = (x : R) • c := rfl

/-- 被約な終域では、根イデアルのテンソルから終域への標準射は単射。
終域の正則性・平坦性を仮定しない。 -/
theorem compatibleRootIdealTensorMap_injective
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (C : Type u) [CommRing C] [Algebra R C] [IsReduced C] :
    Function.Injective (compatibleRootIdealTensorMap ρ C) := by
  have hzero : ∀ z : compatibleRootIdeal ρ ⊗[R] C,
      compatibleRootIdealTensorMap ρ C z = 0 → z = 0 := by
    intro z hz
    obtain ⟨n, c, rfl⟩ := compatibleRootIdeal_tensor_singleStage ρ hρ z
    have hmul : algebraMap R C (ρ n) * c = 0 := by
      simpa only [compatibleRootIdealTensorMap_tmul, compatibleRootIdealElement,
        Algebra.smul_def] using hz
    have hρC : ∀ m, (algebraMap R C (ρ (m + 1))) ^ p = algebraMap R C (ρ m) := by
      intro m
      rw [← map_pow, hρ]
    have hkill := compatibleRoot_transition_kills_kernel
      (fun m ↦ algebraMap R C (ρ m)) hρC n c hmul
    have he : compatibleRootIdealElement ρ n =
        ρ (n + 1) ^ (p - 1) • compatibleRootIdealElement ρ (n + 1) := by
      apply Subtype.ext
      change ρ n = ρ (n + 1) ^ (p - 1) * ρ (n + 1)
      rw [← hρ n, ← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).pos]
    rw [he, TensorProduct.smul_tmul]
    have hs : ρ (n + 1) ^ (p - 1) • c = 0 := by
      rw [Algebra.smul_def, map_pow]
      exact hkill
    rw [hs, TensorProduct.tmul_zero]
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hxy, sub_self]

end SerrePositivity.BhattScholze
