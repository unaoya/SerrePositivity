module

public import SerrePositivity.CommutativeAlgebra.FinitePresentationCommonLocalizationModel
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal

/-! # Finite presentation common models for actual localized splittings -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- A localized splitting gives a finite, finitely presented common model with
both original maps, their support bounds and one common cokernel exponent. -/
theorem localizationSplitting_exists_finitePresentation_common_model_bounds
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L)) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      Module.Finite R E ∧ Algebra.FinitePresentation R E ∧ Module.FinitePresentation R E ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E) (w : E →ₐ[R] (Fin r → L)),
        (∀ a, w (u a) = e ((1 : L) ⊗ₜ[R] a)) ∧
        (∀ b i, w (v b) i = algebraMap R L (b i)) ∧
        IsLocalizedModule (.powers d) w.toLinearMap ∧
        u.toRingHom.Finite ∧ v.toRingHom.Finite ∧
        (∀ a, u a = 0 → ∃ n : ℕ, d ^ n • a = 0) ∧
        (∀ b, v b = 0 → ∃ n : ℕ, d ^ n • b = 0) ∧
        ∃ n : ℕ, (∀ y : E ⧸ u.toLinearMap.range, d ^ n • y = 0) ∧
          (∀ y : E ⧸ v.toLinearMap.range, d ^ n • y = 0) := by
  let f : A →ₐ[R] (Fin r → L) := (e.toAlgHom.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[R] L ⊗[R] A)
  let h : (Fin r → R) →ₐ[R] (Fin r → L) :=
    AlgHom.pi (fun i => (Algebra.ofId R L).comp (Pi.evalAlgHom R (fun _ : Fin r => R) i))
  have hf : f.toLinearMap = (e.restrictScalars R).toLinearEquiv.toLinearMap.comp
      (TensorProduct.mk R L A 1) := by ext x i; rfl
  let : IsLocalizedModule (.powers d) f.toLinearMap := by
    rw [hf]
    exact IsLocalizedModule.of_linearEquiv (.powers d) (TensorProduct.mk R L A 1)
      (e.restrictScalars R).toLinearEquiv
  let q := TensorProduct.piScalarRight R L L (Fin r)
  have hh : h.toLinearMap = (q.restrictScalars R).toLinearMap.comp
      (TensorProduct.mk R L (Fin r → R) 1) := by
    apply LinearMap.ext
    intro x
    apply funext
    intro i
    change algebraMap R L (x i) = (x i) • (1 : L)
    simp only [Algebra.smul_def, mul_one]
  let : IsLocalizedModule (.powers d) h.toLinearMap := by
    rw [hh]
    exact IsLocalizedModule.of_linearEquiv (.powers d)
      (TensorProduct.mk R L (Fin r → R) 1) (q.restrictScalars R)
  obtain ⟨E, hE, aE, hfinite, hfp, hmfp, u, v, w, hu, hv, hloc⟩ :=
    exists_finitePresentation_common_localization_model d f h
  let : Module.Finite R E := hfinite
  let : IsLocalizedModule (.powers d) w.toLinearMap := hloc
  have huF : u.toRingHom.Finite := RingHom.Finite.of_comp_finite
    (show (u.toRingHom.comp (algebraMap R A)).Finite from by
      change ((u : A →+* E).comp (algebraMap R A)).Finite
      rw [u.comp_algebraMap]
      exact RingHom.finite_algebraMap.mpr hfinite)
  have hvF : v.toRingHom.Finite := RingHom.Finite.of_comp_finite
    (show (v.toRingHom.comp (algebraMap R (Fin r → R))).Finite from by
      change ((v : (Fin r → R) →+* E).comp (algebraMap R (Fin r → R))).Finite
      rw [v.comp_algebraMap]
      exact RingHom.finite_algebraMap.mpr hfinite)
  have hu' : w.toLinearMap.comp u.toLinearMap = f.toLinearMap :=
    congrArg AlgHom.toLinearMap hu
  have hv' : w.toLinearMap.comp v.toLinearMap = h.toLinearMap :=
    congrArg AlgHom.toLinearMap hv
  refine ⟨E, hE, aE, hfinite, hfp, hmfp, u, v, w, ?_, ?_, hloc, huF, hvF, ?_, ?_, ?_⟩
  · intro a
    exact AlgHom.congr_fun hu a
  · intro b i
    exact congrArg (fun z : Fin r → L => z i) (AlgHom.congr_fun hv b)
  · exact fun a ha => localizationComparison_ker_power_torsion d
      u.toLinearMap f.toLinearMap w.toLinearMap hu' a ha
  · exact fun b hb => localizationComparison_ker_power_torsion d
      v.toLinearMap h.toLinearMap w.toLinearMap hv' b hb
  · exact localizationComparisons_exists_common_pow_annihilates_cokers_of_localized_target d
      u.toLinearMap v.toLinearMap f.toLinearMap h.toLinearMap w.toLinearMap hu' hv'

end SerrePositivity
