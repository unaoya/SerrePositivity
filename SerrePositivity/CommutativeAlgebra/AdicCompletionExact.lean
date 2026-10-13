module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionInjective

/-! # 一様なフィルトレーション比較の下での完備化の完全性

Noether 性・有限性を使う Artin–Rees の入力を、一様な比較条件へ分離する。
右全射な完全列では、その比較条件から完備化した列の完全性を導く。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open LinearMap Submodule AdicCompletion

/-- 一様なフィルトレーション比較と右全射性があれば、完備化は完全性を保つ。
加群の有限性・環の Noether 性は要求せず、比較条件の供給側に分離する。 -/
theorem adicCompletion_map_exact_of_uniform_filtration_bound
    {R M N P : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (I : Ideal R)
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hbound : ∃ k : ℕ, ∀ n : ℕ,
      Submodule.comap f (I ^ (n + k) • (⊤ : Submodule R N)) ≤
        I ^ n • (⊤ : Submodule R M)) :
    Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) := by
  obtain ⟨k, hk⟩ := hbound
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ (fun y ↦ ?_)
  · rw [AdicCompletion.map_comp, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
  · apply AdicCompletion.induction_on I N y (fun b ↦ ?_)
    intro hz
    have hb (n : ℕ) : g (b n) ∈ (I ^ n • ⊤ : Submodule R P) := by
      simpa using congrArg (fun x ↦ x.val n) hz
    have hlift (n : ℕ) : ∃ a : M,
        f a - b (k + n) ∈ (I ^ (k + n) • ⊤ : Submodule R N) := by
      have hmem : g (b (k + n)) ∈ Submodule.map g
          (I ^ (k + n) • ⊤ : Submodule R N) := by
        rw [map_smul'', Submodule.map_top, range_eq_top.mpr hg]
        exact hb (k + n)
      obtain ⟨d, hdmem, hd⟩ := hmem
      obtain ⟨a, ha⟩ := (hfg (b (k + n) - d)).mp (by simp [hd])
      exact ⟨a, by simpa [ha] using (I ^ (k + n) • (⊤ : Submodule R N)).neg_mem hdmem⟩
    choose a ha using hlift
    have hstep (n : ℕ) : a (n + 1) - a n ∈ (I ^ n • ⊤ : Submodule R M) := by
      apply hk n
      change f (a (n + 1) - a n) ∈ (I ^ (n + k) • (⊤ : Submodule R N))
      have hle : (I ^ (k + (n + 1)) • ⊤ : Submodule R N) ≤
          I ^ (k + n) • ⊤ :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
      have hdelta : b (k + (n + 1)) - b (k + n) ∈
          (I ^ (k + n) • ⊤ : Submodule R N) := by
        rw [← Submodule.Quotient.eq]
        exact AdicCauchySequence.mk_eq_mk (by omega) b
      have hsum := (I ^ (k + n) • (⊤ : Submodule R N)).sub_mem
        ((I ^ (k + n) • (⊤ : Submodule R N)).add_mem (hle (ha (n + 1))) hdelta) (ha n)
      convert hsum using 1 <;> simp [map_sub, Nat.add_comm]
    refine ⟨AdicCompletion.mk I M (AdicCauchySequence.mk I M a ?_), ?_⟩
    · intro n
      apply SModEq.symm
      simpa only [SModEq.sub_mem] using hstep n
    · ext n
      suffices he : Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (f (a n)) =
          Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (b (k + n)) by
        simp [he, AdicCauchySequence.mk_eq_mk (show n ≤ k + n by omega)]
      rw [Submodule.Quotient.eq]
      exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (show n ≤ k + n by omega))) (ha n)

end SerrePositivity
