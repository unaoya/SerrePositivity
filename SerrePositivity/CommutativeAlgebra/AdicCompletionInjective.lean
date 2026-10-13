module

public import Mathlib.RingTheory.AdicCompletion.Exactness

/-! # フィルトレーションの一様な比較による完備化写像の単射性

Noether 性や加群の有限性を完備化写像の単射性の直接の仮定にしない。
像の誘導フィルトレーションと元のフィルトレーションの一様な比較を、
その比較を供給する Artin–Rees 型の議論から分離する。
-/

@[expose] public section
universe u
namespace SerrePositivity
open LinearMap

/-- 誘導フィルトレーションが一様なずれで元のフィルトレーションに含まれるなら、
完備化した写像は単射。有限性・Noether 性は比較の供給側にのみ必要となる。 -/
theorem adicCompletion_map_injective_of_uniform_filtration_bound
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (I : Ideal R) (f : M →ₗ[R] N)
    (hbound : ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap f (I ^ (n + k) • (⊤ : Submodule R N)) ≤
        I ^ n • (⊤ : Submodule R M)) :
    Function.Injective (AdicCompletion.map I f) := by
  obtain ⟨k, hk⟩ := hbound
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x
  apply AdicCompletion.induction_on I M x (fun a ↦ ?_)
  intro hx
  refine AdicCompletion.mk_zero_of _ _ _ ⟨0, fun n _ ↦ ⟨n + k, by omega, n, by omega, ?_⟩⟩
  apply hk n
  simpa using congrArg (fun x ↦ x.val (n + k)) hx

/-- 有限な終域をもつ単射には Artin–Rees による一様な比較がある。
比較そのものを公開し、完備化の単射性とは独立に再利用できるようにする。 -/
theorem exists_uniform_filtration_bound_of_finite
    {R M N : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R N] (I : Ideal R) (f : M →ₗ[R] N) (hf : Function.Injective f) :
    ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap f (I ^ (n + k) • (⊤ : Submodule R N)) ≤
        I ^ n • (⊤ : Submodule R M) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (range f)
  refine ⟨k, fun n ↦ ?_⟩
  intro x hx
  rw [← Submodule.comap_map_eq_of_injective hf (I ^ n • ⊤ : Submodule R M),
    Submodule.map_smul'', Submodule.map_top]
  apply (smul_mono_right _ inf_le_right :
    I ^ n • (I ^ k • ⊤ ⊓ range f) ≤ _) (show f x ∈ _ from ?_)
  nth_rw 1 [show n = n + k - k by omega]
  rw [← hk (n + k) (show n + k ≥ k by omega)]
  exact ⟨hx, ⟨x, rfl⟩⟩

end SerrePositivity
