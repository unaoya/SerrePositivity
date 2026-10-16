module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Finiteness.Basic

/-! # A finite common model for two algebras in the same localization

The common intermediate algebra is the image of their tensor product, with both
original maps and the actual embedding into the common localized algebra retained.
This constructs ordinary integral comparison data; it asserts no almost invariance.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct

/-- Two finite algebras mapping into one localized algebra have a finite common
intermediate algebra inside that target, and the target is its module localization. -/
theorem exists_finite_common_localization_model
    {R A B T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T]
    [Module.Finite R A] [Module.Finite R B]
    (S : Submonoid R) (f : A →ₐ[R] T) (h : B →ₐ[R] T)
    [IsLocalizedModule S f.toLinearMap] :
    ∃ E : Subalgebra R T, Module.Finite R E ∧
      IsLocalizedModule S E.val.toLinearMap ∧
      ∃ (u : A →ₐ[R] E) (v : B →ₐ[R] E),
        E.val.comp u = f ∧ E.val.comp v = h ∧
          u.toRingHom.Finite ∧ v.toRingHom.Finite := by
  let ψ : A ⊗[R] B →ₐ[R] T :=
    Algebra.TensorProduct.lift f h (fun _ _ => Commute.all _ _)
  let E : Subalgebra R T := ψ.range
  let u : A →ₐ[R] E := ψ.rangeRestrict.comp (Algebra.TensorProduct.includeLeft : A →ₐ[R] _)
  let v : B →ₐ[R] E := ψ.rangeRestrict.comp (Algebra.TensorProduct.includeRight : B →ₐ[R] _)
  have hu : E.val.comp u = f := by
    ext x
    change ψ (x ⊗ₜ[R] (1 : B)) = f x
    simp only [ψ, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  have hv : E.val.comp v = h := by
    ext x
    change ψ ((1 : A) ⊗ₜ[R] x) = h x
    simp only [ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hfinite : Module.Finite R E :=
    Module.Finite.of_surjective ψ.rangeRestrict.toLinearMap ψ.rangeRestrict_surjective
  have hloc : IsLocalizedModule S E.val.toLinearMap := by
    constructor
    · exact IsLocalizedModule.map_units (S := S) (f := f.toLinearMap)
    · intro t
      obtain ⟨⟨a, s⟩, ha⟩ := IsLocalizedModule.surj S f.toLinearMap t
      refine ⟨(u a, s), ?_⟩
      change s • t = E.val (u a)
      rw [show E.val (u a) = f a from RingHom.congr_fun (congrArg AlgHom.toRingHom hu) a]
      exact ha
    · intro x y hxy
      refine ⟨1, ?_⟩
      have he : x = y := Subtype.ext hxy
      simpa only [one_smul] using he
  have huF : u.toRingHom.Finite := RingHom.Finite.of_comp_finite
    (show (u.toRingHom.comp (algebraMap R A)).Finite from by
      change ((u : A →+* E).comp (algebraMap R A)).Finite
      rw [u.comp_algebraMap]
      exact RingHom.finite_algebraMap.mpr hfinite)
  have hvF : v.toRingHom.Finite := RingHom.Finite.of_comp_finite
    (show (v.toRingHom.comp (algebraMap R B)).Finite from by
      change ((v : B →+* E).comp (algebraMap R B)).Finite
      rw [v.comp_algebraMap]
      exact RingHom.finite_algebraMap.mpr hfinite)
  exact ⟨E, hfinite, hloc, u, v, hu, hv, huF, hvF⟩

/-- A splitting over any localization gives a finite common model inside the
specified localized algebra, with both original coefficient maps. -/
theorem localizationSplitting_exists_finite_common_model
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (S : Submonoid R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization S L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L)) :
    ∃ E : Subalgebra R (Fin r → L), Module.Finite R E ∧
      IsLocalizedModule S E.val.toLinearMap ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
        (∀ a, E.val (u a) = e ((1 : L) ⊗ₜ[R] a)) ∧
        (∀ b i, E.val (v b) i = algebraMap R L (b i)) ∧
          u.toRingHom.Finite ∧ v.toRingHom.Finite := by
  let f : A →ₐ[R] (Fin r → L) := (e.toAlgHom.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[R] L ⊗[R] A)
  let h : (Fin r → R) →ₐ[R] (Fin r → L) :=
    AlgHom.pi (fun i => (Algebra.ofId R L).comp (Pi.evalAlgHom R (fun _ : Fin r => R) i))
  have hf : f.toLinearMap = (e.restrictScalars R).toLinearEquiv.toLinearMap.comp
      (TensorProduct.mk R L A 1) := by
    ext x i
    rfl
  let : IsLocalizedModule S f.toLinearMap := by
    rw [hf]
    exact IsLocalizedModule.of_linearEquiv S (TensorProduct.mk R L A 1)
      (e.restrictScalars R).toLinearEquiv
  obtain ⟨E, hfinite, hloc, u, v, hu, hv, huF, hvF⟩ :=
    exists_finite_common_localization_model S f h
  refine ⟨E, hfinite, hloc, u, v, ?_, ?_, huF, hvF⟩
  · intro a
    exact AlgHom.congr_fun hu a
  · intro b i
    exact congrArg (fun z : Fin r → L => z i) (AlgHom.congr_fun hv b)

/-- A specified splitting after inverting g supplies an actual finite common model
for the original algebra and the trivial finite product, including rank zero. -/
theorem principalSplitting_exists_finite_common_model
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (g : R) (r : ℕ)
    (e : (Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
      (Fin r → Localization.Away g)) :
    ∃ E : Subalgebra R (Fin r → Localization.Away g), Module.Finite R E ∧
      IsLocalizedModule (.powers g) E.val.toLinearMap ∧
      ∃ (u : A →ₐ[R] E) (v : (Fin r → R) →ₐ[R] E),
        (∀ a, E.val (u a) = e ((1 : Localization.Away g) ⊗ₜ[R] a)) ∧
        (∀ b i, E.val (v b) i = algebraMap R (Localization.Away g) (b i)) ∧
          u.toRingHom.Finite ∧ v.toRingHom.Finite :=
  localizationSplitting_exists_finite_common_model (.powers g) (Localization.Away g) r e

end SerrePositivity
