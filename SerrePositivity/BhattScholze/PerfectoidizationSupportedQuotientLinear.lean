module

public import SerrePositivity.BhattScholze.PerfectoidizationSupportedQuotientKernel
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationAlgebraMap
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Original scalar actions on the kernel and cokernel of the actual comparison

This is the linear-map interface for Tor comparison and derived-cone descent.
The original algebra structures over R are retained throughout.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {R A B C D : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] {f : A →ₐ[R] C} {g : B →ₐ[R] D}

/-- The actual R-linear comparison has almost-zero kernel and zero cokernel.
The sole existence citation is the existing BS Theorem 7.14. -/
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
