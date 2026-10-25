module

public import SerrePositivity.CommutativeAlgebra.PerfectoidizationSupportedQuotient
public import SerrePositivity.CommutativeAlgebra.CompletelyFaithfullyFlatInjective
public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealCompatibleRoots
public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealFunctor
public import SerrePositivity.BhattScholze.Andre.AndreFlatness
public import SerrePositivity.BhattScholze.Semiperfectoid.PerfectoidizationSurjectiveMap

/-! # Almost kernel support for perfectoidizations of actual surjections

André's existing Theorem 7.14 supplies an injective AIC perfectoid test extension.
The common proof then applies to the actual functorial comparison. The
comparison is surjective by B4, so its cokernel vanishes. General integral
modifications remain separate statements.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    {p : ℕ} [Fact p.Prime] {f : A →+* C} {g : B →+* D}

/-- Each given compatible root kills the actual comparison kernel. The only
existence input is the existing André perfectoid AIC extension. -/
theorem perfectoidization_map_kernel_roots_of_surjective_supported_kernel
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (hq : Function.Surjective q)
    (ρ : ℕ → A) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a ∈ RingHom.ker q, ∃ N : ℕ, ρ 0 ^ N * a = 0) :
    ∀ n, ∀ x : C, IsPerfectoidization.map hf hg q x = 0 → f (ρ n) * x = 0 := by
  obtain ⟨E, hEring, hEalg, hE, hflat, hAIC⟩ :=
    Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed C p hf.1
  letI := hEring
  letI := hEalg
  let := hf.1.isAdicComplete C p
  have hj : Function.Injective (algebraMap C E) :=
    algebraMap_injective_of_completelyFaithfullyFlat_of_isHausdorff C E (p : C) hflat
  exact hf.map_kernel_roots_of_surjective_supported_kernel_of_injective_aic hg q hq
    (algebraMap C E) hj hE hAIC ρ hρ hk

/-- The original perfectoid ideal of the image generator annihilates the entire
actual comparison kernel, with no bounded-torsion condition on that kernel. -/
theorem perfectoidization_map_kernel_ideal_of_surjective_supported_kernel
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (hq : Function.Surjective q)
    (ρ : ℕ → A) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a ∈ RingHom.ker q, ∃ N : ℕ, ρ 0 ^ N * a = 0) :
    ∀ s ∈ perfectoidIdeal C p hf.1 (f (ρ 0)), ∀ x : C,
      IsPerfectoidization.map hf hg q x = 0 → s * x = 0 := by
  let := hf.1.isAdicComplete C p
  let σ : ℕ → C := fun n => f (ρ n)
  have hσ : ∀ n, σ (n + 1) ^ p = σ n := by
    intro n
    change f (ρ (n + 1)) ^ p = f (ρ n)
    rw [← map_pow, hρ]
  have hroots := perfectoidization_map_kernel_roots_of_surjective_supported_kernel
    hf hg q hq ρ hρ hk
  intro s hs x hx
  let J := (Ideal.span {x}).annihilator
  let : IsAdicComplete (Ideal.span {(p : C ⧸ J)}) (C ⧸ J) :=
    annihilatorPrincipalQuotient_isAdicComplete C p x
  have hJ : perfectoidIdeal C p hf.1 (σ 0) ≤ J :=
    (perfectoidIdeal_le_iff_compatible_roots_of_quotient_isHausdorff C p hf.1 σ hσ J).mpr
      (fun n => (Submodule.mem_annihilator_span_singleton x _).mpr (hroots n x hx))
  exact (Submodule.mem_annihilator_span_singleton x s).mp (hJ hs)

/-- The original base ideal, through the original coefficient map, kills the
comparison kernel; no new scalar action or coefficient ring is substituted. -/
theorem perfectoidization_map_kernel_originalIdeal_of_surjective_supported_kernel
    (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
    (α : R →+* A) (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (hq : Function.Surjective q)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a ∈ RingHom.ker q, ∃ N : ℕ, α (ρ 0) ^ N * a = 0) :
    ∀ s ∈ perfectoidIdeal R p hR (ρ 0), ∀ x : C,
      IsPerfectoidization.map hf hg q x = 0 → f (α s) * x = 0 := by
  let σ : ℕ → A := fun n => α (ρ n)
  have hσ : ∀ n, σ (n + 1) ^ p = σ n := by
    intro n
    change α (ρ (n + 1)) ^ p = α (ρ n)
    rw [← map_pow, hρ]
  intro s hs x hx
  have hs' := map_mem_perfectoidIdeal p hR hf.1 (f.comp α) (ρ 0) s hs
  exact perfectoidization_map_kernel_ideal_of_surjective_supported_kernel
    hf hg q hq σ hσ hk (f (α s)) hs' x hx

/-- A supported surjection gives an actual surjective almost comparison after
perfectoidization. The ideal and its scalar action come from the original base. -/
theorem perfectoidization_map_almost_of_surjective_supported_kernel
    (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
    (α : R →+* A) (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (hq : Function.Surjective q)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a ∈ RingHom.ker q, ∃ N : ℕ, α (ρ 0) ^ N * a = 0) :
    Function.Surjective (IsPerfectoidization.map hf hg q) ∧
      ∀ s ∈ perfectoidIdeal R p hR (ρ 0), ∀ x : C,
        IsPerfectoidization.map hf hg q x = 0 → f (α s) * x = 0 :=
  ⟨perfectoidization_map_surjective_of_surjective hf hg q hq,
    perfectoidization_map_kernel_originalIdeal_of_surjective_supported_kernel
      R hR α hf hg q hq ρ hρ hk⟩

end SerrePositivity.BhattScholze
