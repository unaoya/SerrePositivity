module
public import SerrePositivity.KTheory.LatticeClass
public import SerrePositivity.CommutativeAlgebra.SubmoduleExact

/-! # Supported lattices in short exact sequences -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {P : Submonoid R} {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
  {N₁ N₂ N₃ : Type u} [AddCommGroup N₁] [Module R N₁]
  [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]

namespace SupportedLocalizationLattice
/-- The preimage of the middle lattice under the injective map. -/
def preimage (L : SupportedLocalizationLattice P Z N₂)
    (f : N₁ →ₗ[R] N₂) (hf : Function.Injective f) : SupportedLocalizationLattice P Z N₁ := by
  let F : L.carrier.comap f →ₗ[R] L.carrier := f.restrict (fun _ h => h)
  have hi : Function.Injective F := submoduleRestriction_injective L.carrier f hf
  have : Module.Finite R (L.carrier.comap f) := Module.Finite.of_injective F hi
  refine ⟨L.carrier.comap f, Module.Finite.iff_fg.mp inferInstance,
    (Module.support_subset_of_injective F hi).trans L.support, ?_⟩
  intro n
  obtain ⟨s, hs⟩ := L.denominators (f n)
  exact ⟨s, by simpa only [Submodule.mem_comap, map_smul] using hs⟩

/-- The image of the middle lattice under the surjective map. -/
def image (L : SupportedLocalizationLattice P Z N₂)
    (g : N₂ →ₗ[R] N₃) (hg : Function.Surjective g) : SupportedLocalizationLattice P Z N₃ := by
  let G : L.carrier →ₗ[R] L.carrier.map g :=
    g.restrict (fun _ h => Submodule.mem_map_of_mem h)
  have hs : Function.Surjective G := submoduleImage_restrict_surjective L.carrier g
  refine ⟨L.carrier.map g, L.fg.map g,
    (Module.support_subset_of_surjective G hs).trans L.support, ?_⟩
  intro n
  obtain ⟨m, rfl⟩ := hg n
  obtain ⟨s, hs⟩ := L.denominators m
  exact ⟨s, Submodule.mem_map.mpr ⟨(s : R) • m, hs, g.map_smul _ _⟩⟩

/-- Pullback and image give a short exact sequence of finite supported lattices. -/
def shortExact (L : SupportedLocalizationLattice P Z N₂)
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (hf : Function.Injective f) (he : Function.Exact f g) (hg : Function.Surjective g) :
    SupportedModuleShortExact Z := by
  let F : (L.preimage f hf).carrier →ₗ[R] L.carrier := f.restrict (fun _ h => h)
  let G : L.carrier →ₗ[R] (L.image g hg).carrier :=
    g.restrict (fun _ h => Submodule.mem_map_of_mem h)
  refine
    { left := (L.preimage f hf).obj
      middle := L.obj
      right := (L.image g hg).obj
      f := F
      g := G
      injective := submoduleRestriction_injective L.carrier f hf
      exact := submoduleRestriction_exact L.carrier f g he
      surjective := submoduleImage_restrict_surjective L.carrier g }

/-- Additivity for the lattices obtained by preimage and image. -/
lemma class_shortExact (L : SupportedLocalizationLattice P Z N₂)
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (hf : Function.Injective f) (he : Function.Exact f g) (hg : Function.Surjective g) :
    LocalizationG0Quotient.mk (P := P) L.obj =
      LocalizationG0Quotient.mk (P := P) (L.preimage f hf).obj +
        LocalizationG0Quotient.mk (P := P) (L.image g hg).obj := by
  simpa only [shortExact] using
    LocalizationG0Quotient.mk_shortExact (P := P) (L.shortExact f g hf he hg)
end SupportedLocalizationLattice
end SerrePositivity
