module
public import SerrePositivity.CommutativeAlgebra.ScalarIsogeny
public import SerrePositivity.CommutativeAlgebra.Idempotent
public import SerrePositivity.HomologicalAlgebra.TorCoefficientIdeal
public import SerrePositivity.HomologicalAlgebra.TorAlgebraScalarComparison

/-! # Original Tor coefficient actions from a finite free comparison -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]

/-- Kernel and cokernel annihilators kill positive Tor by their product.
The coefficient ring C need not be finite; the test module N is arbitrary. -/
lemma torCoefficientScalar_eq_zero_of_finiteFree_comparison
    (r : ℕ) (f : C →ₗ[R] (Fin r → R)) (a b : R)
    (ha : ∀ y : (Fin r → R) ⧸ f.range, a • y = 0)
    (hb : ∀ x : f.ker, b • x = 0)
    (N : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C (a * b)) = 0 := by
  obtain ⟨v, hv⟩ := exists_scalar_factorization_through_finiteFree r f a b ha hb
  let F := (Tor (ModuleCat.{u} R) i).flip.obj N
  have hz : IsZero (F.obj (ModuleCat.of R (Fin r → R))) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (torModule_subsingleton_of_flat (R := R) (Fin r → R) N j)
  have hm : ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R C (a * b))) =
      (ModuleCat.ofHom f) ≫ (ModuleCat.ofHom v) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun hv x
    change v (f x) = (a * b) • x at h
    change algebraMap R C (a * b) * x = v (f x)
    simpa only [Algebra.smul_def] using h.symm
  change F.map (ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R C (a * b)))) = 0
  rw [hm, CategoryTheory.Functor.map_comp, hz.eq_of_tgt (F.map (ModuleCat.ofHom f)) 0,
    zero_comp]

/-- An annihilator of the test module acts by the original coefficient scalar as zero on Tor. -/
lemma torCoefficientScalar_algebraMap_eq_zero_of_annihilates
    (N : ModuleCat.{u} R) (i : ℕ) (a : R) (ha : ∀ x : N, a • x = 0) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C a) = 0 := by
  apply (torAlgebraComparison_scalar_zero_iff_forall N i (algebraMap R C a)).mpr
  intro x
  exact torAlg_smul_eq_zero (algebraMap R C) i N a ha x

/-- An ideal annihilating kernel and cokernel acts by its square as zero on every positive Tor. -/
lemma torCoefficientScalar_eq_zero_of_finiteFree_ideal_square
    (r : ℕ) (f : C →ₗ[R] (Fin r → R)) (I : Ideal R)
    (hc : ∀ a ∈ I, ∀ y : (Fin r → R) ⧸ f.range, a • y = 0)
    (hk : ∀ b ∈ I, ∀ x : f.ker, b • x = 0)
    (N : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i) (s : R) (hs : s ∈ I * I) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  let F := (Tor (ModuleCat.{u} R) i).flip.obj N
  have hsq : I * I ≤ (coefficientFunctorAnnihilator (C := C) F).comap (algebraMap R C) := by
    apply Ideal.mul_le.mpr
    intro a ha b hb
    exact torCoefficientScalar_eq_zero_of_finiteFree_comparison r f a b (hc a ha) (hk b hb) N i hi
  exact hsq hs

/-- Modulo an annihilator of the test module, idempotence removes the square loss.
All positive degrees and arbitrary test modules are retained. -/
lemma torCoefficientScalar_eq_zero_of_finiteFree_almost_comparison
    (r : ℕ) (f : C →ₗ[R] (Fin r → R)) (I : Ideal R)
    (hc : ∀ a ∈ I, ∀ y : (Fin r → R) ⧸ f.range, a • y = 0)
    (hk : ∀ b ∈ I, ∀ x : f.ker, b • x = 0)
    (N : ModuleCat.{u} R) (a : R) (ha : ∀ x : N, a • x = 0)
    (hid : IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a}))))
    (i : ℕ) (hi : 0 < i) (s : R) (hs : s ∈ I) :
    torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  let F := (Tor (ModuleCat.{u} R) i).flip.obj N
  let J := (coefficientFunctorAnnihilator (C := C) F).comap (algebraMap R C)
  have hK : Ideal.span {a} ≤ J := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact torCoefficientScalar_algebraMap_eq_zero_of_annihilates N i a ha
  have hsq : I * I ≤ J := by
    intro x hx
    exact torCoefficientScalar_eq_zero_of_finiteFree_ideal_square r f I hc hk N i hi x hx
  have hI := ideal_le_pow_sup_of_quotient_image_idempotent I (Ideal.span {a}) 2 (by decide) hid
  exact hI.trans (sup_le (by simpa only [pow_two] using hsq) hK) hs

end SerrePositivity
