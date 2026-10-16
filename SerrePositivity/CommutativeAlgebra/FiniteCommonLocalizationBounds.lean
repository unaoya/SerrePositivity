module

public import SerrePositivity.CommutativeAlgebra.FiniteCommonLocalizationModel
public import SerrePositivity.CommutativeAlgebra.LocalizationComparisonBounds

/-! # Ordinary support bounds for the actual finite common comparison maps

Both comparison cokernels have one exponent, while the kernels are pointwise
power torsion. No bound after perfectoidization or uniform bound across towers
is inferred from these ordinary finite-module estimates.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct

/-- A specified localized splitting yields actual finite comparisons whose two
cokernels share one exponent and whose kernels are power torsion. -/
theorem localizationSplitting_exists_finite_common_model_bounds
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L)) :
    ∃ E : Subalgebra R (Fin r → L), Module.Finite R E ∧
      IsLocalizedModule (.powers d) E.val.toLinearMap ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
        (∀ a, E.val (u a) = e ((1 : L) ⊗ₜ[R] a)) ∧
        (∀ b i, E.val (v b) i = algebraMap R L (b i)) ∧
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
      (TensorProduct.mk R L A 1) := by
    ext x i
    rfl
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
  obtain ⟨E, hfinite, hloc, u, v, hu, hv, huF, hvF⟩ :=
    localizationSplitting_exists_finite_common_model (.powers d) L r e
  let : Module.Finite R E := hfinite
  have hcomp : E.val.toLinearMap.comp u.toLinearMap = f.toLinearMap := by
    ext a i
    exact congrArg (fun z : Fin r → L => z i) (hu a)
  have hcomp' : E.val.toLinearMap.comp v.toLinearMap = h.toLinearMap := by
    apply LinearMap.ext
    intro b
    apply funext
    intro i
    exact hv b i
  have hinj : Function.Injective E.val.toLinearMap := Subtype.val_injective
  refine ⟨E, hfinite, hloc, u, v, hu, hv, huF, hvF, ?_, ?_, ?_⟩
  · intro a ha
    exact localizationComparison_ker_power_torsion d u.toLinearMap f.toLinearMap
      E.val.toLinearMap hcomp a ha
  · intro b hb
    exact localizationComparison_ker_power_torsion d v.toLinearMap h.toLinearMap
      E.val.toLinearMap hcomp' b hb
  · exact localizationComparisons_exists_common_pow_annihilates_cokers d
      u.toLinearMap v.toLinearMap f.toLinearMap h.toLinearMap E.val.toLinearMap hinj hcomp hcomp'

end SerrePositivity
