module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionExact
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Algebra.Operations

/-! # 平坦テンソル積へのフィルトレーション比較の移送 -/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity
open LinearMap Submodule
variable {R M N P : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]

/-- イデアル倍部分加群のテンソル像は、テンソル積の同じイデアル倍。平坦性は不要。 -/
theorem range_rTensor_smul_top (I : Ideal R) :
    range ((I • (⊤ : Submodule R M)).subtype.rTensor P) =
      I • (⊤ : Submodule R (M ⊗[R] P)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa using (I • (⊤ : Submodule R (M ⊗[R] P))).add_mem hx hy
    | tmul m p =>
      change (m : M) ⊗ₜ[R] p ∈ _
      refine Submodule.smul_induction_on m.property ?_ ?_
      · intro r hr m hm
        rw [← TensorProduct.smul_tmul']
        exact Submodule.smul_mem_smul hr (Submodule.mem_top)
      · intro x y hx hy
        simpa [TensorProduct.add_tmul] using
          (I • (⊤ : Submodule R (M ⊗[R] P))).add_mem hx hy
  · intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr x hx
      clear hx
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simpa [smul_add] using (range _).add_mem hx hy
      | tmul m p =>
        refine ⟨(⟨r • m, Submodule.smul_mem_smul hr (Submodule.mem_top)⟩ :
          ↥(I • (⊤ : Submodule R M))) ⊗ₜ[R] p, ?_⟩
        simpa using (TensorProduct.smul_tmul' r m p).symm
    · intro x y hx hy
      exact (range _).add_mem hx hy

/-- 平坦テンソル積は部分加群の逆像を保つ。 -/
theorem comap_range_rTensor_subtype [Module.Flat R P]
    (f : M →ₗ[R] N) (Q : Submodule R N) :
    (range (Q.subtype.rTensor P)).comap (f.rTensor P) =
      range ((Q.comap f).subtype.rTensor P) := by
  have hfg : Function.Exact (Q.comap f).subtype (Q.mkQ.comp f) := by
    intro x
    simp [Submodule.mem_comap]
  have ht := Module.Flat.rTensor_exact P hfg
  rw [← LinearMap.exact_iff.mp ht]
  rw [LinearMap.rTensor_comp, LinearMap.ker_comp,
    rTensor_mkQ]

/-- 一様なフィルトレーション比較は平坦なテンソル積に同じ次数のずれで移る。 -/
theorem rTensor_uniform_filtration_bound [Module.Flat R P]
    (I : Ideal R) (f : M →ₗ[R] N) (k : ℕ)
    (hk : ∀ n : ℕ, (I ^ (n + k) • (⊤ : Submodule R N)).comap f ≤
      I ^ n • (⊤ : Submodule R M)) :
    ∀ n : ℕ, (I ^ (n + k) • (⊤ : Submodule R (N ⊗[R] P))).comap
      (f.rTensor P) ≤ I ^ n • (⊤ : Submodule R (M ⊗[R] P)) := by
  intro n
  rw [← range_rTensor_smul_top, comap_range_rTensor_subtype, ← range_rTensor_smul_top]
  rintro _ ⟨x, rfl⟩
  exact ⟨((Submodule.inclusion (hk n)).rTensor P) x, by
    rw [← LinearMap.rTensor_comp_apply]
    rfl⟩

/-- Artin–Rees の一様な比較を、平坦な加群とのテンソル積へ移す。 -/
theorem exists_rTensor_uniform_filtration_bound [IsNoetherianRing R]
    [Module.Finite R N] [Module.Flat R P]
    (I : Ideal R) (f : M →ₗ[R] N) (hf : Function.Injective f) :
    ∃ k : ℕ, ∀ n : ℕ, (I ^ (n + k) • (⊤ : Submodule R (N ⊗[R] P))).comap
      (f.rTensor P) ≤ I ^ n • (⊤ : Submodule R (M ⊗[R] P)) := by
  obtain ⟨k, hk⟩ := exists_uniform_filtration_bound_of_finite I f hf
  exact ⟨k, rTensor_uniform_filtration_bound I f k hk⟩

/-- 有限終域の単射を平坦加群とテンソルし、完備化しても単射となる。 -/
theorem adicCompletion_rTensor_injective_of_finite [IsNoetherianRing R]
    [Module.Finite R N] [Module.Flat R P]
    (I : Ideal R) (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (AdicCompletion.map I (f.rTensor P)) :=
  adicCompletion_map_injective_of_uniform_filtration_bound I (f.rTensor P)
    (exists_rTensor_uniform_filtration_bound I f hf)

/-- 有限な中間加群をもつ短完全列は、平坦テンソル積と完備化の後も完全。 -/
theorem adicCompletion_rTensor_exact_of_finite
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    [IsNoetherianRing R] [Module.Finite R N] [Module.Flat R P]
    (I : Ideal R) (f : M →ₗ[R] N) (g : N →ₗ[R] Q)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (AdicCompletion.map I (f.rTensor P))
      (AdicCompletion.map I (g.rTensor P)) :=
  adicCompletion_map_exact_of_uniform_filtration_bound I (f.rTensor P) (g.rTensor P)
    (Module.Flat.rTensor_exact P hfg) (LinearMap.rTensor_surjective P hg)
    (exists_rTensor_uniform_filtration_bound I f hf)

end SerrePositivity
