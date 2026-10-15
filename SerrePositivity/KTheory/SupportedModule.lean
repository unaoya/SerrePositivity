module

public import SerrePositivity.CommutativeAlgebra.ModuleSupport
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Noetherian.Basic

/-! # Finitely generated modules with closed support

Objects retain their ambient `ModuleCat` morphisms. Noetherian hypotheses are
needed for arbitrary submodules, but not for quotients or extensions.
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory
variable {R : Type u} [CommRing R]

/-- Finite generation and closed support, as a property of ambient modules. -/
def finiteModuleSupportedOn (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    ObjectProperty (ModuleCat.{u} R) := fun M =>
  Module.Finite R M ∧ Module.support R M ⊆ Z

abbrev SupportedFGModuleOn (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :=
  (finiteModuleSupportedOn Z).FullSubcategory

instance {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} (M : SupportedFGModuleOn Z) :
    Module.Finite R M.obj := M.property.1

namespace finiteModuleSupportedOn
variable {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
  {M N L : ModuleCat.{u} R}

lemma mono (h : finiteModuleSupportedOn Z M) (hZW : Z ≤ W) :
    finiteModuleSupportedOn W M := ⟨h.1, h.2.trans hZW⟩

lemma of_iso (e : M ≅ N) (h : finiteModuleSupportedOn Z M) :
    finiteModuleSupportedOn Z N := by
  have :=  h.1
  refine ⟨Module.Finite.of_surjective e.hom.hom e.toLinearEquiv.surjective, ?_⟩
  rw [← e.toLinearEquiv.support_eq]
  exact h.2

instance (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    (finiteModuleSupportedOn Z).IsClosedUnderIsomorphisms where
  of_iso e h := of_iso e h

lemma of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (h : finiteModuleSupportedOn Z M) : finiteModuleSupportedOn Z N := by
  have :=  h.1
  exact ⟨Module.Finite.of_surjective f hf,
    (Module.support_subset_of_surjective f hf).trans h.2⟩

lemma of_injective [IsNoetherianRing R] (f : M →ₗ[R] N)
    (hf : Function.Injective f) (h : finiteModuleSupportedOn Z N) :
    finiteModuleSupportedOn Z M := by
  have :=  h.1
  exact ⟨Module.Finite.of_injective f hf,
    (Module.support_subset_of_injective f hf).trans h.2⟩

lemma of_exact (f : M →ₗ[R] N) (g : N →ₗ[R] L)
    (he : Function.Exact f g) (hg : Function.Surjective g)
    (hM : finiteModuleSupportedOn Z M) (hL : finiteModuleSupportedOn Z L) :
    finiteModuleSupportedOn Z N := by
  have :=  hM.1
  have :=  hL.1
  exact ⟨Module.Finite.of_exact he hg,
    (module_support_subset_union_of_exact f g he).trans (Set.union_subset hM.2 hL.2)⟩

lemma submodule [IsNoetherianRing R] (h : finiteModuleSupportedOn Z M)
    (U : Submodule R M) : finiteModuleSupportedOn Z (ModuleCat.of R U) :=
  of_injective U.subtype U.subtype_injective h

lemma quotient (h : finiteModuleSupportedOn Z M) (U : Submodule R M) :
    finiteModuleSupportedOn Z (ModuleCat.of R (M ⧸ U)) :=
  of_surjective U.mkQ U.mkQ_surjective h

lemma of_subsingleton [Module.Finite R M] [Subsingleton M] :
    finiteModuleSupportedOn Z M := by
  exact ⟨inferInstance, by simp [Module.support_eq_empty]⟩

lemma bot_iff : finiteModuleSupportedOn ⊥ M ↔ Module.Finite R M ∧ Subsingleton M := by
  simp only [finiteModuleSupportedOn, TopologicalSpace.Closeds.coe_bot,
    Set.subset_empty_iff, Module.support_eq_empty_iff]

lemma top_iff : finiteModuleSupportedOn ⊤ M ↔ Module.Finite R M := by
  simp [finiteModuleSupportedOn]

end finiteModuleSupportedOn

/-- Bundle a finite module with a proof of its support. -/
def supportedFGModuleOnObj (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (M : ModuleCat.{u} R) (h : finiteModuleSupportedOn Z M) : SupportedFGModuleOn Z :=
  ⟨M, h⟩

end SerrePositivity
