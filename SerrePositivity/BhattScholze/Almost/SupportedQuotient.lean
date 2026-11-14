module

public import SerrePositivity.BhattScholze.Semiperfectoid.AbsolutelyIntegrallyClosedQuotient
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Cover
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.BhattScholze.Andre.AndreFlatness
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralExistence
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# 全射の perfectoid 化の比較写像の almost 性（CLMST が使う比較補題）

## 概要
全射に沿う perfectoid 化の比較写像の核・余核は perfectoid イデアルで零化される。有限比較の像への全射部分。

## 方針
André の補題で絶対整閉な試験拡大を作り、BS 著者版 Theorem 7.4 で余核を消す。

## 規約
原典の項目ではない。

## 使われ方
CLMST の Tor 比較。
-/

universe u

/-! ## Almost kernel support for perfectoidizations of actual surjections

André's existing BS 著者版 Theorem 7.14 supplies an injective AIC perfectoid test extension.
The common proof then applies to the actual functorial comparison. The
comparison is surjective by B4, so its cokernel vanishes. General integral
modifications remain separate statements.
-/

@[expose] public noncomputable section PerfectoidizationSupportedQuotientKernel

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

end PerfectoidizationSupportedQuotientKernel

/-! ## Original scalar actions on the kernel and cokernel of the actual comparison

This is the linear-map interface for Tor comparison and derived-cone descent.
The original algebra structures over R are retained throughout.
-/

@[expose] public noncomputable section PerfectoidizationSupportedQuotientLinear

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {R A B C D : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] {f : A →ₐ[R] C} {g : B →ₐ[R] D}

/-- The actual R-linear comparison has almost-zero kernel and zero cokernel.
The sole existence citation is the existing BS 著者版 Theorem 7.14. -/
theorem perfectoidization_mapAlgHom_ker_coker_annihilated_of_surjective_supported_kernel
    (hR : IsIntegralPerfectoid R p)
    (hf : IsPerfectoidization p f.toRingHom) (hg : IsPerfectoidization p g.toRingHom)
    (q : A →ₐ[R] B) (hq : Function.Surjective q)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a ∈ RingHom.ker q.toRingHom, ∃ N : ℕ, (algebraMap R A (ρ 0)) ^ N * a = 0) :
    (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
      ∀ x : (IsPerfectoidization.mapAlgHom hf hg q).toLinearMap.ker, s • x = 0) ∧
    (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
      ∀ y : D ⧸ (IsPerfectoidization.mapAlgHom hf hg q).toLinearMap.range, s • y = 0) := by
  let l := (IsPerfectoidization.mapAlgHom hf hg q).toLinearMap
  obtain ⟨hsurj, hker⟩ := perfectoidization_map_almost_of_surjective_supported_kernel
    R hR (algebraMap R A) hf hg q.toRingHom hq ρ hρ hk
  constructor
  · intro s hs x
    apply Subtype.ext
    change s • (x : C) = 0
    rw [Algebra.smul_def]
    have hx : IsPerfectoidization.map hf hg q.toRingHom (x : C) = 0 := x.property
    have h := hker s hs (x : C) hx
    change f (algebraMap R A s) * (x : C) = 0 at h
    rw [f.commutes] at h
    exact h
  · have hrange : l.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have : Subsingleton (D ⧸ l.range) :=
      (Submodule.Quotient.subsingleton_iff (p := l.range)).mpr hrange
    exact fun _ _ _ => Subsingleton.elim _ _

end SerrePositivity.BhattScholze

end PerfectoidizationSupportedQuotientLinear

/-! ## The actual supported quotient onto the image of a finite comparison

This constructs the surjective part of a modification comparison. It does not
assume or assert almost invariance of the remaining injective inclusion.
-/

@[expose] public noncomputable section PerfectoidizationImageComparison

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {R A E C D : Type u}
    [CommRing R] [CommRing A] [CommRing E] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R E] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] {f : A →ₐ[R] C}

/-- The original comparison to its actual image gives a supported surjection,
so its universal perfectoidizations have almost-zero kernel and cokernel. -/
theorem perfectoidization_image_ker_coker_annihilated
    (hR : IsIntegralPerfectoid R p) (φ : A →ₐ[R] E)
    (hf : IsPerfectoidization p f.toRingHom)
    (g : φ.range →ₐ[R] D) (hg : IsPerfectoidization p g.toRingHom)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a, φ a = 0 → ∃ N : ℕ, ρ 0 ^ N • a = 0) :
    (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
      ∀ x : (IsPerfectoidization.mapAlgHom hf hg φ.rangeRestrict).toLinearMap.ker, s • x = 0) ∧
    (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
      ∀ y : D ⧸ (IsPerfectoidization.mapAlgHom hf hg φ.rangeRestrict).toLinearMap.range,
        s • y = 0) := by
  apply perfectoidization_mapAlgHom_ker_coker_annihilated_of_surjective_supported_kernel
    hR hf hg φ.rangeRestrict φ.rangeRestrict_surjective ρ hρ
  intro a ha
  have hφ : φ a = 0 := congrArg (fun x : φ.range => (x : E)) ha
  obtain ⟨N, hN⟩ := hk a hφ
  refine ⟨N, ?_⟩
  simpa only [Algebra.smul_def, map_pow] using hN

/-- Choose the image perfectoidization once, before every test object. The
existence input is the existing integral-perfectoidization citation B-I. -/
theorem exists_image_perfectoidization_almost_comparison
    [Module.Finite R A] (hR : IsIntegralPerfectoid R p) (φ : A →ₐ[R] E)
    (hf : IsPerfectoidization p f.toRingHom)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hk : ∀ a, φ a = 0 → ∃ N : ℕ, ρ 0 ^ N • a = 0) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D) (g : φ.range →ₐ[R] D),
      ∃ hg : IsPerfectoidization p g.toRingHom,
        (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
          ∀ x : (IsPerfectoidization.mapAlgHom hf hg φ.rangeRestrict).toLinearMap.ker,
            s • x = 0) ∧
        (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
          ∀ y : D ⧸ (IsPerfectoidization.mapAlgHom hf hg φ.rangeRestrict).toLinearMap.range,
            s • y = 0) := by
  let : Module.Finite R φ.range := Module.Finite.of_surjective
    φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  obtain ⟨D, hD, g, hg⟩ := Inputs.exists_perfectoidization_of_integral R φ.range p hR
  let := hD
  let : Algebra R D := (g.comp (algebraMap R φ.range)).toAlgebra
  let g' : φ.range →ₐ[R] D := { g with commutes' := fun _ => rfl }
  exact ⟨D, hD, inferInstance, g', hg,
    perfectoidization_image_ker_coker_annihilated hR φ hf g' hg ρ hρ hk⟩

/-- The actual image comparison factors the actual original comparison, over R. -/
theorem perfectoidization_image_factorization
    (φ : A →ₐ[R] E) (hf : IsPerfectoidization p f.toRingHom)
    (g : φ.range →ₐ[R] D) (hg : IsPerfectoidization p g.toRingHom)
    {F : Type u} [CommRing F] [Algebra R F]
    (h : E →ₐ[R] F) (hh : IsPerfectoidization p h.toRingHom) :
    (IsPerfectoidization.mapAlgHom hg hh φ.range.val).comp
      (IsPerfectoidization.mapAlgHom hf hg φ.rangeRestrict) =
        IsPerfectoidization.mapAlgHom hf hh φ := by
  rw [IsPerfectoidization.mapAlgHom_mapAlgHom, AlgHom.val_comp_rangeRestrict]

end SerrePositivity.BhattScholze

end PerfectoidizationImageComparison
