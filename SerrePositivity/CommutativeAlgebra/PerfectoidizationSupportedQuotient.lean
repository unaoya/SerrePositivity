module

public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedPerfectoidQuotient
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor

/-! # Kernel support survives perfectoidization of an actual surjection

Perfectoid annihilator quotients are test objects for the original universal maps.
An injective map to an absolutely integrally closed perfectoid ring suffices.
No existence of that extension is assumed or cited by the common statements.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.IsPerfectoidization
variable {A B C D E : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [CommRing E] {p : ℕ} [Fact p.Prime]
    {f : A →+* C} {g : B →+* D}

/-- If an actual surjection has a power-torsion kernel, every compatible root kills
the kernel of its actual perfectoidization comparison, detected in an injective AIC extension. -/
theorem map_kernel_roots_of_surjective_supported_kernel_of_injective_aic
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (hq : Function.Surjective q)
    (j : C →+* E) (hj : Function.Injective j)
    (hE : IsIntegralPerfectoid E p) (hAIC : IsAbsolutelyIntegrallyClosed E)
    (ρ : ℕ → A) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a ∈ RingHom.ker q, ∃ N : ℕ, ρ 0 ^ N * a = 0) :
    ∀ n, ∀ x : C, map hf hg q x = 0 → f (ρ n) * x = 0 := by
  let := hE.isReduced E p
  intro n x hx
  have hkill (a : A) (ha : a ∈ RingHom.ker q) : j (f (ρ n)) * j (f a) = 0 := by
    obtain ⟨N, hN⟩ := hk a ha
    let J := (Ideal.span {j (f a)}).annihilator
    have hJ : J.IsRadical := annihilatorPrincipal_isRadical_of_reduced E (j (f a))
    have hbase : j (f (ρ 0)) ∈ J := by
      apply hJ
      refine ⟨N, ?_⟩
      apply (Submodule.mem_annihilator_span_singleton (j (f a)) _).mpr
      change j (f (ρ 0)) ^ N * j (f a) = 0
      simpa only [RingHom.comp_apply, map_mul, map_pow, map_zero] using congrArg (j.comp f) hN
    have hroot : j (f (ρ n)) ∈ J := by
      apply hJ
      refine ⟨p ^ n, ?_⟩
      have hpow : ρ n ^ (p ^ n) = ρ 0 := by
        simpa only [Nat.zero_add] using compatibleRoots_pow p ρ hρ 0 n
      rw [← map_pow, ← map_pow, hpow]
      exact hbase
    exact (Submodule.mem_annihilator_span_singleton (j (f a)) _).mp hroot
  let I := (Ideal.span {j (f (ρ n))}).annihilator
  let Q := E ⧸ I
  let π : E →+* Q := Ideal.Quotient.mk I
  have hQ : IsIntegralPerfectoid Q p :=
    aicPerfectoid_annihilatorPrincipalQuotient E p hE hAIC (j (f (ρ n)))
  let k : A →+* Q := (π.comp j).comp f
  have hker : RingHom.ker q ≤ RingHom.ker k := by
    intro a ha
    change π (j (f a)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (Submodule.mem_annihilator_span_singleton (j (f (ρ n))) _).mpr
    change j (f a) * j (f (ρ n)) = 0
    rw [mul_comm]
    exact hkill a ha
  let b : B →+* Q := q.liftOfSurjective hq ⟨k, hker⟩
  have hb : b.comp q = k := q.liftOfSurjective_comp hq ⟨k, hker⟩
  let l : D →+* Q := hg.lift hQ b
  have hl : l.comp g = b := hg.lift_comp hQ b
  let m := map hf hg q
  have hmf : m.comp f = g.comp q := map_comp hf hg q
  have hfac : (l.comp m).comp f = k := by
    rw [RingHom.comp_assoc, hmf, ← RingHom.comp_assoc, hl, hb]
  have he : l.comp m = π.comp j :=
    (hf.lift_unique hQ k (l.comp m) hfac).trans
      (hf.lift_unique hQ k (π.comp j) rfl).symm
  have hz := RingHom.congr_fun he x
  change l (m x) = π (j x) at hz
  change m x = 0 at hx
  rw [hx, map_zero] at hz
  have hmem : j x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz.symm
  have hmul := (Submodule.mem_annihilator_span_singleton (j (f (ρ n))) (j x)).mp hmem
  apply hj
  rw [map_mul, map_zero]
  simpa only [smul_eq_mul, mul_comm] using hmul

/-- The source perfectoidization itself can serve as the absolutely integrally closed test ring. -/
theorem map_kernel_roots_of_surjective_supported_kernel_of_aic
    (hf : IsPerfectoidization p f) (hg : IsPerfectoidization p g)
    (q : A →+* B) (hq : Function.Surjective q) (hC : IsAbsolutelyIntegrallyClosed C)
    (ρ : ℕ → A) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a ∈ RingHom.ker q, ∃ N : ℕ, ρ 0 ^ N * a = 0) :
    ∀ n, ∀ x : C, map hf hg q x = 0 → f (ρ n) * x = 0 :=
  hf.map_kernel_roots_of_surjective_supported_kernel_of_injective_aic hg q hq
    (RingHom.id C) Function.injective_id hf.1 hC ρ hρ hk

end SerrePositivity.IsPerfectoidization
