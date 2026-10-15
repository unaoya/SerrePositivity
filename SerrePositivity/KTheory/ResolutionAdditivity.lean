module
public import SerrePositivity.KTheory.ResolutionClass
public import SerrePositivity.HomologicalAlgebra.ResolutionMappingCone

/-! # Resolution classes are additive on short exact sequences -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits HomologicalComplex
variable {R : Type u} [CommRing R] {M₁ M₂ M₃ : ModuleCat.{u} R}

namespace PerfectModuleResolution
variable (F : PerfectModuleResolution M₁) (G : PerfectModuleResolution M₂)
  (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (l : F.complex ⟶ G.complex)
  (hl : homologyMap l 0 = F.resolution.homologyZeroIso.hom ≫ ModuleCat.ofHom f ≫
    G.resolution.homologyZeroIso.inv)

/-- Zero homology of a lifted cone identifies with the cokernel module. -/
def coneHomologyZeroEquiv (hg : Function.Surjective g) (he : Function.Exact f g) :
    (CochainComplex.mappingCone l).homology 0 ≃ₗ[R] M₃ :=
  F.resolution.coneHomologyZeroEquiv G.resolution f g l hl hg he

/-- The cone of a lifted short exact sequence resolves its last module. -/
def mappingCone (hf : Function.Injective f) (hg : Function.Surjective g)
    (he : Function.Exact f g) : PerfectModuleResolution M₃ where
  complex := CochainComplex.mappingCone l
  perfect := strictlyPerfectComplex_mappingCone R l F.perfect G.perfect
  resolution := F.resolution.mappingCone G.resolution f g l hl hf hg he
end PerfectModuleResolution

variable [HasFiniteProjectiveResolutions R]
lemma resClass_shortExact {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (E : SupportedModuleShortExact Z) : resClass E.middle = resClass E.left + resClass E.right := by
  let F := chosenPerfectModuleResolution E.left.obj
  let G := chosenPerfectModuleResolution E.middle.obj
  obtain ⟨l, hl⟩ := F.exists_comparison G (ModuleCat.ofHom E.f)
  have hl' : homologyMap l 0 = F.resolution.homologyZeroIso.hom ≫ ModuleCat.ofHom E.f ≫
      G.resolution.homologyZeroIso.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact hl
  let C := F.mappingCone G E.f E.g l hl' E.injective E.surjective E.exact
  rw [resClass_eq E.left F, resClass_eq E.middle G, resClass_eq E.right C]
  have hc : C.k0Class Z E.right.property.2 =
      G.k0Class Z E.middle.property.2 - F.k0Class Z E.left.property.2 := by
    exact K0WithSupport.mk_cone Z _ _ F.perfect G.perfect
      (F.support E.left.property.2) (G.support E.middle.property.2) l
  rw [hc]
  abel

namespace G0WithSupport
/-- The resolution homomorphism from supported G₀ to supported K₀. -/
def resolutionMap (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    G0WithSupport Z →+ K0WithSupport Z := lift resClass resClass_iso resClass_shortExact

@[simp] lemma resolutionMap_mk (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (M : SupportedFGModuleOn Z) : resolutionMap Z (mk M) = resClass M := lift_mk ..
end G0WithSupport
end SerrePositivity
