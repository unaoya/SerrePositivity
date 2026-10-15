module

public import SerrePositivity.HomologicalAlgebra.ConeLES
public import SerrePositivity.HomologicalAlgebra.Resolution

/-! # Mapping cones of maps between module resolutions -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits HomologicalComplex
variable {R : Type u} [CommRing R] {M₁ M₂ M₃ : ModuleCat.{u} R}
namespace IsResolutionOf
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}
variable (hK : IsResolutionOf K M₁) (hL : IsResolutionOf L M₂)
  (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (l : K ⟶ L)
  (hl : homologyMap l 0 = hK.homologyZeroIso.hom ≫ ModuleCat.ofHom f ≫
    hL.homologyZeroIso.inv)

/-- Zero homology of a lifted cone is the cokernel module. -/
def coneHomologyZeroEquiv (hg : Function.Surjective g) (he : Function.Exact f g) :
    (CochainComplex.mappingCone l).homology 0 ≃ₗ[R] M₃ := by
  have h₂ := Cone.exact₂ l 0
  have h₃ := Cone.exact₃ l 0 1 rfl
  have hepi : Epi (homologyMap (CochainComplex.mappingCone.inr l) 0) :=
    h₃.epi_f ((hK.isZero_homology 1 one_ne_zero).eq_zero_of_tgt _)
  have hsurj := (ModuleCat.epi_iff_surjective _).mp hepi
  have hrk : LinearMap.range (homologyMap l 0).hom =
      LinearMap.ker (homologyMap (CochainComplex.mappingCone.inr l) 0).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h₂
  let e₁ := hK.homologyZeroIso.toLinearEquiv
  let e₂ := hL.homologyZeroIso.toLinearEquiv
  have hmap : (LinearMap.range (homologyMap l 0).hom).map e₂.toLinearMap = LinearMap.range f := by
    rw [← LinearMap.range_comp, hl]
    have hc : e₂.toLinearMap.comp
        (hK.homologyZeroIso.hom ≫ ModuleCat.ofHom f ≫
          hL.homologyZeroIso.inv).hom = f.comp e₁.toLinearMap := by
      ext x
      simp [e₁, e₂]
    rw [hc, LinearMap.range_comp_of_range_eq_top _ e₁.range]
  exact (LinearMap.quotKerEquivOfSurjective _ hsurj).symm.trans
    ((Submodule.quotEquivOfEq _ _ hrk.symm).trans
      ((Submodule.Quotient.equiv _ _ e₂ hmap).trans
        ((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp he).symm).trans
          (LinearMap.quotKerEquivOfSurjective g hg))))

end IsResolutionOf
end SerrePositivity
