module
public import SerrePositivity.CommutativeAlgebra.ScalarIsogenyInverse
public import SerrePositivity.HomologicalAlgebra.TorFiniteFreeComparisonAnnihilator
public import Mathlib.RingTheory.Ideal.Colon

/-! # Original Tor ideal actions through almost comparisons in either direction -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R C D : Type u} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D]

private lemma torScalar_zero_of_scalar_factorization
    (f : C →ₗ[R] D) (v : D →ₗ[R] C) (r c : R)
    (hv : f.comp v = r • LinearMap.id)
    (N : ModuleCat.{u} R) (i : ℕ)
    (hc : torCoefficientScalarEndomorphism C N i (algebraMap R C c) = 0) :
    torCoefficientScalarEndomorphism D N i (algebraMap R D (r * c)) = 0 := by
  let F := (Tor (ModuleCat.{u} R) i).flip.obj N
  have hm : ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R D (r * c))) =
      (ModuleCat.ofHom v) ≫
        (ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R C c))) ≫ ModuleCat.ofHom f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hh := LinearMap.congr_fun hv x
    change f (v x) = r • x at hh
    change algebraMap R D (r * c) * x = f (algebraMap R C c * v x)
    rw [← Algebra.smul_def (r * c) x, ← Algebra.smul_def c (v x), f.map_smul, hh, smul_smul]
    rw [mul_comm r c]
  change F.map (ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R D (r * c)))) = 0
  change F.map (ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R C c))) = 0 at hc
  rw [hm, Functor.map_comp, Functor.map_comp, hc, zero_comp, comp_zero]

private lemma torIdeal_zero_of_triple_products
    (I : Ideal R) (N : ModuleCat.{u} R) (a : R) (ha : ∀ x : N, a • x = 0)
    (hid : IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a})))) (i : ℕ)
    (hprod : ∀ x ∈ I, ∀ y ∈ I, ∀ z ∈ I,
      torCoefficientScalarEndomorphism D N i (algebraMap R D (x * y * z)) = 0) :
    ∀ s ∈ I, torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0 := by
  let F := (Tor (ModuleCat.{u} R) i).flip.obj N
  let J := (coefficientFunctorAnnihilator (C := D) F).comap (algebraMap R D)
  have hcolon : I * I ≤ J.colon (I : Set R) := by
    apply Ideal.mul_le.mpr
    intro x hx y hy
    apply Submodule.mem_colon.mpr
    intro z hz
    exact hprod x hx y hy z hz
  have hcube : I ^ 3 ≤ J := by
    rw [show I ^ 3 = (I * I) * I by simp only [pow_succ, pow_zero, one_mul]]
    apply Ideal.mul_le.mpr
    intro x hx z hz
    exact Submodule.mem_colon.mp (hcolon hx) z hz
  have haJ : Ideal.span {a} ≤ J := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact torCoefficientScalar_algebraMap_eq_zero_of_annihilates N i a ha
  have hI := ideal_le_pow_sup_of_quotient_image_idempotent I (Ideal.span {a}) 3 (by decide) hid
  exact hI.trans (sup_le hcube haJ)

/-- An actual comparison with almost-zero kernel and cokernel preserves the entire
ideal's zero action on original Tor, in both directions and in every degree.
The test module is arbitrary apart from its stated annihilator. -/
theorem torCoefficientIdeal_eq_zero_iff_of_almost_comparison
    (f : C →ₗ[R] D) (I : Ideal R)
    (hk : ∀ a ∈ I, ∀ x : f.ker, a • x = 0)
    (hc : ∀ b ∈ I, ∀ y : D ⧸ f.range, b • y = 0)
    (N : ModuleCat.{u} R) (a : R) (ha : ∀ x : N, a • x = 0)
    (hid : IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a})))) (i : ℕ) :
    (∀ s ∈ I, torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
      ∀ s ∈ I, torCoefficientScalarEndomorphism D N i (algebraMap R D s) = 0 := by
  constructor
  · intro hC
    apply torIdeal_zero_of_triple_products I N a ha hid i
    intro x hx y hy z hz
    obtain ⟨v, _hC, hD⟩ := exists_scalar_inverse_of_ker_coker_annihilated f x y (hk x hx) (hc y hy)
    exact torScalar_zero_of_scalar_factorization f v (x * y) z hD N i (hC z hz)
  · intro hD
    apply torIdeal_zero_of_triple_products I N a ha hid i
    intro x hx y hy z hz
    obtain ⟨v, hC, _hD⟩ := exists_scalar_inverse_of_ker_coker_annihilated f x y (hk x hx) (hc y hy)
    exact torScalar_zero_of_scalar_factorization v f (x * y) z hC N i (hD z hz)

/-- A reverse finite-free comparison also supplies all positive Tor zero actions.
There is no requirement for a single almost-isomorphism pointing from C to the free module. -/
theorem torCoefficientScalar_eq_zero_of_reverse_finiteFree_almost_comparison
    (r : ℕ) (f : (Fin r → R) →ₗ[R] C) (I : Ideal R)
    (hk : ∀ a ∈ I, ∀ x : f.ker, a • x = 0)
    (hc : ∀ b ∈ I, ∀ y : C ⧸ f.range, b • y = 0)
    (N : ModuleCat.{u} R) (a : R) (ha : ∀ x : N, a • x = 0)
    (hid : IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a}))))
    (i : ℕ) (hi : 0 < i) (s : R) (hs : s ∈ I) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  have hz : IsZero (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R (Fin r → R))).obj N) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (torModule_subsingleton_of_flat (R := R) (Fin r → R) N j)
  have hfree : ∀ x ∈ I,
      torCoefficientScalarEndomorphism (Fin r → R) N i
        (algebraMap R (Fin r → R) x) = 0 :=
    fun _ _ => hz.eq_of_src _ _
  exact ((torCoefficientIdeal_eq_zero_iff_of_almost_comparison
    f I hk hc N a ha hid i).mp hfree) s hs

end SerrePositivity
