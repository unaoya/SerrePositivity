import SerrePositivity.KTheory.ResolutionAdditivity
import SerrePositivity.HomologicalAlgebra.TorLES
import Mathlib.Util.AssertNoSorry

open CategoryTheory HomologicalComplex SerrePositivity
universe u
variable {R : Type u} [CommRing R] {M₁ M₂ M₃ : ModuleCat.{u} R}

example (F : PerfectModuleResolution M₁) (G : PerfectModuleResolution M₂)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (l : F.complex ⟶ G.complex)
    (hl : homologyMap l 0 = F.resolution.homologyZeroIso.hom ≫ ModuleCat.ofHom f ≫
      G.resolution.homologyZeroIso.inv)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g) :
    (F.mappingCone G f g l hl hf hg he).resolution =
      F.resolution.mappingCone G.resolution f g l hl hf hg he := rfl

assert_no_sorry SerrePositivity.IsResolutionOf.mappingCone
assert_no_sorry SerrePositivity.PerfectModuleResolution.mappingCone
assert_no_sorry SerrePositivity.isResolutionOf_cone
assert_no_sorry SerrePositivity.resClass_shortExact
#print axioms SerrePositivity.IsResolutionOf.mappingCone
#print axioms SerrePositivity.isResolutionOf_cone
