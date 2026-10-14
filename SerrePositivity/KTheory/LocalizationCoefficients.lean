module
public import SerrePositivity.KTheory.LocalizationKernelSupport
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Supported localization after extending coefficients -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity
open scoped TensorProduct
variable (E : Type v) [CommRing E]

/-- Extend an additive group map to an E-linear map after tensoring over the integers. -/
def g0CoefficientMap {A C : Type*} [AddCommGroup A] [AddCommGroup C] (f : A →+ C) :
    E ⊗[ℤ] A →ₗ[E] E ⊗[ℤ] C := f.toIntLinearMap.baseChange E

@[simp] lemma g0CoefficientMap_tmul {A C : Type*} [AddCommGroup A] [AddCommGroup C]
    (f : A →+ C) (a : E) (x : A) : g0CoefficientMap E f (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] f x := rfl

lemma g0CoefficientMap_comp {A C D : Type*} [AddCommGroup A] [AddCommGroup C] [AddCommGroup D]
    (f : A →+ C) (g : C →+ D) :
    (g0CoefficientMap E g).comp (g0CoefficientMap E f) = g0CoefficientMap E (g.comp f) := by
  ext a
  rfl

/-- A characteristic-zero coefficient field is flat over the integers. -/
lemma coefficientField_flat (F : Type v) [Field F] [CharZero F] : Module.Flat ℤ F := inferInstance

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  (P : Submonoid R) [IsLocalization P B]
  (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

namespace G0WithSupport
abbrev Coefficients := E ⊗[ℤ] G0WithSupport Z

/-- Localization with extended coefficients. -/
def coefficientLocalize : Coefficients E Z →ₗ[E]
    Coefficients E (supportPullback (algebraMap R B) Z) :=
  g0CoefficientMap E (localize P Z _ le_rfl)

/-- The torsion subgroup's inclusion with extended coefficients. -/
def coefficientTorsionInclusion : E ⊗[ℤ] localizationTorsionSubgroup P Z →ₗ[E] Coefficients E Z :=
  g0CoefficientMap E (localizationTorsionSubgroup P Z).subtype

/-- Coefficient extension of the support enlargement map. -/
def coefficientEnlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) :
    Coefficients E Z →ₗ[E] Coefficients E W := g0CoefficientMap E (enlarge h)

@[simp] lemma coefficientEnlarge_tmul {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z ≤ W) (a : E) (x : G0WithSupport Z) :
    coefficientEnlarge E h (a ⊗ₜ[ℤ] x) = a ⊗ₜ[ℤ] enlarge h x := rfl

lemma coefficientEnlarge_comp {Z W V : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z ≤ W) (h' : W ≤ V) :
    (coefficientEnlarge E h').comp (coefficientEnlarge E h) =
      coefficientEnlarge E (h.trans h') := by
  rw [coefficientEnlarge, coefficientEnlarge, g0CoefficientMap_comp, enlarge_comp]
  rfl

variable [IsNoetherianRing R]
/-- Right exactness survives extension of coefficients. No left injectivity is asserted. -/
lemma coefficientLocalize_exact : Function.Exact (coefficientTorsionInclusion E P Z)
    (coefficientLocalize (B := B) E P Z) := by
  have he : Function.Exact (localizationTorsionSubgroup P Z).subtype.toIntLinearMap
      (localize (S := B) P Z (supportPullback (algebraMap R B) Z) le_rfl).toIntLinearMap := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [← localize_ker (B := B) P Z]
      exact hx
    · rintro ⟨x, rfl⟩
      have hx := x.property
      exact (localizationTorsionSubgroup_le_ker
        (B := B) (P := P) (Z := Z) _ le_rfl) hx
  exact lTensor_exact E he (localize_surjective (B := B) P Z)

lemma coefficientLocalize_surjective : Function.Surjective (coefficientLocalize (B := B) E P Z) :=
  LinearMap.lTensor_surjective E (localize_surjective (B := B) P Z)

lemma coefficientLocalize_ker_range : (coefficientLocalize (B := B) E P Z).ker =
    (coefficientTorsionInclusion E P Z).range :=
  (LinearMap.exact_iff.mp (coefficientLocalize_exact (B := B) E P Z))

/-- A coefficient class comes from one support cut out by a denominator. -/
def HasPrincipalCoefficientSupport (x : Coefficients E Z) : Prop :=
  ∃ s ∈ P, ∃ y : Coefficients E (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
    coefficientEnlarge E inf_le_left y = x

namespace HasPrincipalCoefficientSupport
variable {E P Z}
omit [IsNoetherianRing R] in
lemma add {x x' : Coefficients E Z} (hx : HasPrincipalCoefficientSupport E P Z x)
    (hx' : HasPrincipalCoefficientSupport E P Z x') :
    HasPrincipalCoefficientSupport E P Z (x + x') := by
  obtain ⟨s, hs, y, hy⟩ := hx
  obtain ⟨t, ht, y', hy'⟩ := hx'
  let h₁ : Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤
      Z ⊓ supportZeroLocus (Ideal.span ({s * t} : Set R)) :=
    inf_le_inf_left Z (supportZeroLocus_mul_left s t)
  let h₂ : Z ⊓ supportZeroLocus (Ideal.span ({t} : Set R)) ≤
      Z ⊓ supportZeroLocus (Ideal.span ({s * t} : Set R)) :=
    inf_le_inf_left Z (supportZeroLocus_mul_right s t)
  refine ⟨s * t, P.mul_mem hs ht,
    coefficientEnlarge E h₁ y + coefficientEnlarge E h₂ y', ?_⟩
  rw [map_add]
  have e₁ : coefficientEnlarge E inf_le_left (coefficientEnlarge E h₁ y) = x := by
    rw [← LinearMap.comp_apply, coefficientEnlarge_comp]
    exact hy
  have e₂ : coefficientEnlarge E inf_le_left (coefficientEnlarge E h₂ y') = x' := by
    rw [← LinearMap.comp_apply, coefficientEnlarge_comp]
    exact hy'
  rw [e₁, e₂]
end HasPrincipalCoefficientSupport

omit [IsNoetherianRing R] in
/-- Tensor induction combines the denominators in a finite sum of pure tensors. -/
lemma coefficientTorsionInclusion_supported
    (t : E ⊗[ℤ] localizationTorsionSubgroup P Z) :
    HasPrincipalCoefficientSupport E P Z (coefficientTorsionInclusion E P Z t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a h =>
    obtain ⟨s, hs, y, hy⟩ := localizationTorsionSubgroup_le_principalSupport P Z h.property
    refine ⟨s, hs, a ⊗ₜ[ℤ] y, ?_⟩
    simp only [coefficientEnlarge_tmul, hy, coefficientTorsionInclusion, g0CoefficientMap_tmul,
      AddSubgroup.subtype_apply]
  | add t t' ht ht' =>
    rw [map_add]
    exact HasPrincipalCoefficientSupport.add ht ht'

/-- A coefficient kernel class still comes from one denominator's vanishing locus. -/
lemma coefficientLocalize_kernel_supported (x : Coefficients E Z)
    (hx : coefficientLocalize (B := B) E P Z x = 0) :
    ∃ s ∈ P, ∃ y : Coefficients E (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))),
      coefficientEnlarge E inf_le_left y = x := by
  obtain ⟨t, ht⟩ := (coefficientLocalize_exact (B := B) E P Z x).mp hx
  rw [← ht]
  exact coefficientTorsionInclusion_supported E P Z t

omit [IsNoetherianRing R] in
/-- Flat coefficients preserve injectivity of the torsion subgroup's tensor inclusion. -/
lemma coefficientTorsionInclusion_injective [Module.Flat ℤ E] :
    Function.Injective (coefficientTorsionInclusion E P Z) :=
  Module.Flat.lTensor_preserves_injective_linearMap
    (localizationTorsionSubgroup P Z).subtype.toIntLinearMap Subtype.val_injective


/-- The principal supported localization sequence remains right exact over E. -/
lemma coefficientLocalize_away_kernel_range (s : R) [IsLocalization.Away s B] :
    (coefficientLocalize (B := B) E (Submonoid.powers s) Z).ker =
      (coefficientEnlarge E (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z
        from inf_le_left)).range := by
  have he : Function.Exact
      (enlarge (show Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R)) ≤ Z
        from inf_le_left)).toIntLinearMap
      (localize (S := B) (Submonoid.powers s) Z
        (supportPullback (algebraMap R B) Z) le_rfl).toIntLinearMap := by
    intro x
    exact Iff.of_eq (congrArg (fun H : AddSubgroup (G0WithSupport Z) => x ∈ H)
      (localize_away_kernel_range (B := B) (Z := Z) s))
  exact LinearMap.exact_iff.mp
    (lTensor_exact E he (localize_surjective (B := B) (Submonoid.powers s) Z))

end G0WithSupport
end SerrePositivity
