import SerrePositivity.KTheory.ResolutionAdditivity
import SerrePositivity.HomologicalAlgebra.ConeResolution
import Mathlib.Util.AssertNoSorry

open CategoryTheory HomologicalComplex SerrePositivity
universe u
variable {R : Type u} [CommRing R] {M₁ M₂ M₃ : ModuleCat.{u} R}

example (F : PerfectModuleResolution M₁) (G : PerfectModuleResolution M₂)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (l : F.complex ⟶ G.complex)
    (hl : homologyMap l 0 = F.resolution.homologyZeroIso.hom ≫ ModuleCat.ofHom f ≫
      G.resolution.homologyZeroIso.inv)
    (hg : Function.Surjective g) (he : Function.Exact f g) :
    F.coneHomologyZeroEquiv G f g l hl hg he =
      F.resolution.coneHomologyZeroEquiv G.resolution f g l hl hg he := rfl

assert_no_sorry SerrePositivity.IsResolutionOf.coneHomologyZeroEquiv
assert_no_sorry SerrePositivity.PerfectModuleResolution.coneHomologyZeroEquiv
assert_no_sorry SerrePositivity.coneHomologyZeroEquiv
#print axioms SerrePositivity.IsResolutionOf.coneHomologyZeroEquiv
