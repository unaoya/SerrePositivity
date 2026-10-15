module
public import SerrePositivity.KTheory.ResolutionAdditivity
public import SerrePositivity.CategoryTheory.AlternatingSum
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Int.Interval

/-! # G₀-valued Euler additivity for bounded supported exact sequences -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}

namespace SupportedFGModuleOn
/-- The image of a map between finite supported modules remains finite and supported. -/
def image {M N : SupportedFGModuleOn Z} (f : M.obj ⟶ N.obj) : SupportedFGModuleOn Z :=
  ⟨Abelian.image f, finiteModuleSupportedOn.of_injective (Abelian.image.ι f).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) N.property⟩

/-- The coimage is a quotient of the finite supported source. -/
def coimage {M N : SupportedFGModuleOn Z} (f : M.obj ⟶ N.obj) : SupportedFGModuleOn Z :=
  ⟨Abelian.coimage f, finiteModuleSupportedOn.of_surjective (Abelian.coimage.π f).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance) M.property⟩
end SupportedFGModuleOn

namespace G0WithSupport
omit [IsNoetherianRing R] in
lemma mk_of_isZero (M : SupportedFGModuleOn Z) (h : IsZero M.obj) : mk M = 0 := by
  have := ModuleCat.subsingleton_of_isZero h
  exact mk_of_subsingleton M

/-- Split an exact pair into the short exact sequence of its two images. -/
lemma mk_exact_images (X₁ X₂ X₃ : SupportedFGModuleOn Z)
    (f : X₁.obj ⟶ X₂.obj) (g : X₂.obj ⟶ X₃.obj) (he : Function.Exact f g) :
    mk X₂ = mk (SupportedFGModuleOn.image f) + mk (SupportedFGModuleOn.image g) := by
  let S := ModuleCat.shortComplexOfCompEqZero f.hom g.hom
    (LinearMap.ext he.apply_apply_eq_zero)
  have hS : S.Exact := ModuleCat.shortComplex_exact _ he
  let S' := ShortComplex.mk (Abelian.image.ι f) g (Abelian.image_ι_comp_eq_zero S.zero)
  have hS' : S'.Exact := (S.exact_iff_exact_image_ι).mp hS
  let S'' := ShortComplex.mk S'.f (Abelian.coimage.π S'.g)
    (Abelian.comp_coimage_π_eq_zero S'.zero)
  have hS'' : S''.ShortExact := { exact := (S'.exact_iff_exact_coimage_π).mp hS' }
  let E : SupportedModuleShortExact Z :=
    { left := SupportedFGModuleOn.image f
      middle := X₂
      right := SupportedFGModuleOn.coimage g
      f := S''.f.hom
      g := S''.g.hom
      injective := (ModuleCat.mono_iff_injective _).mp hS''.mono_f
      exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS''.exact
      surjective := (ModuleCat.epi_iff_surjective _).mp hS''.epi_g }
  have h := mk_shortExact E
  change mk X₂ = mk (SupportedFGModuleOn.image f) + mk (SupportedFGModuleOn.coimage g) at h
  have hci : mk (SupportedFGModuleOn.coimage g) = mk (SupportedFGModuleOn.image g) :=
    mk_iso (Abelian.coimageIsoImage g)
  rw [hci] at h
  exact h
end G0WithSupport

/-- The Euler class of a sequence of finite supported modules. -/
def supportedModuleEuler (X : ℤ → SupportedFGModuleOn Z) : G0WithSupport Z :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤˣ) : ℤ) • G0WithSupport.mk (X i)

/-- A bounded supported long exact sequence gives G₀-valued Euler additivity. -/
lemma supportedModuleEuler_exact_sequence
    (X₁ X₂ X₃ : ℤ → SupportedFGModuleOn Z)
    (α : ∀ i, (X₁ i).obj ⟶ (X₂ i).obj) (β : ∀ i, (X₂ i).obj ⟶ (X₃ i).obj)
    (δ : ∀ i, (X₃ i).obj ⟶ (X₁ (i + 1)).obj)
    (h₂ : ∀ i, Function.Exact (α i) (β i))
    (h₃ : ∀ i, Function.Exact (β i) (δ i))
    (h₁ : ∀ i, Function.Exact (δ i) (α (i + 1)))
    (hb₂ : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (X₂ i).obj)
    (hb₃ : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (X₃ i).obj) :
    supportedModuleEuler X₂ = supportedModuleEuler X₁ + supportedModuleEuler X₃ := by
  let a := fun i => G0WithSupport.mk (SupportedFGModuleOn.image (α i))
  let b := fun i => G0WithSupport.mk (SupportedFGModuleOn.image (β i))
  let d := fun i => G0WithSupport.mk (SupportedFGModuleOn.image (δ i))
  have hfa : Function.HasFiniteSupport a := by
    obtain ⟨p, q, hpq⟩ := hb₂
    apply (Set.finite_Icc p q).subset
    intro i hi
    by_contra hn
    exact hi (G0WithSupport.mk_of_isZero _ (IsZero.of_mono (Abelian.image.ι (α i))
      (hpq i (by simp only [Set.mem_Icc] at hn; omega))))
  have hfb : Function.HasFiniteSupport b := by
    obtain ⟨p, q, hpq⟩ := hb₃
    apply (Set.finite_Icc p q).subset
    intro i hi
    by_contra hn
    exact hi (G0WithSupport.mk_of_isZero _ (IsZero.of_mono (Abelian.image.ι (β i))
      (hpq i (by simp only [Set.mem_Icc] at hn; omega))))
  have hfd : Function.HasFiniteSupport d := by
    obtain ⟨p, q, hpq⟩ := hb₃
    apply (Set.finite_Icc p q).subset
    intro i hi
    by_contra hn
    exact hi (G0WithSupport.mk_of_isZero _ (IsZero.of_epi (Abelian.factorThruImage (δ i))
      (hpq i (by simp only [Set.mem_Icc] at hn; omega))))
  have e₂ (i : ℤ) : G0WithSupport.mk (X₂ i) = a i + b i :=
    G0WithSupport.mk_exact_images _ _ _ (α i) (β i) (h₂ i)
  have e₃ (i : ℤ) : G0WithSupport.mk (X₃ i) = b i + d i :=
    G0WithSupport.mk_exact_images _ _ _ (β i) (δ i) (h₃ i)
  have e₁ (i : ℤ) : G0WithSupport.mk (X₁ i) = d (i - 1) + a i := by
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
    rw [add_sub_cancel_right]
    exact G0WithSupport.mk_exact_images _ _ _ (δ j) (α (j + 1)) (h₁ j)
  unfold supportedModuleEuler
  simp_rw [e₂, e₁, e₃]
  exact alternatingGroupFinsum_exact a b d hfa hfb hfd
end SerrePositivity
