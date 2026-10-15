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

/-- The cone of a lift of an injective map resolves its cokernel module. -/
def mappingCone (hf : Function.Injective f) (hg : Function.Surjective g)
    (he : Function.Exact f g) : IsResolutionOf (CochainComplex.mappingCone l) M₃ :=
    { isZero_X := fun i hi => by
        rw [CochainComplex.mappingCone.isZero_X_iff]
        exact ⟨hK.isZero_X _ (by omega), hL.isZero_X _ hi⟩
      projective := fun i => by
        have := hK.projective (i + 1)
        have := hL.projective i
        exact Projective.of_iso
          (HomologicalComplex.homotopyCofiber.XIsoBiprod l i (i + 1) rfl).symm inferInstance
      isZero_homology := fun i hi => by
        by_cases hi' : i = -1
        · subst i
          have h10 : (-1 : ℤ) + 1 = 0 := by norm_num
          have h₃ := Cone.exact₃ l (-1) 0 h10
          have hz := hL.isZero_homology (-1) (by norm_num)
          have hmonoδ : Mono (Cone.δ l (-1) 0 h10) := h₃.mono_g (hz.eq_zero_of_src _)
          have hcomp : Cone.δ l (-1) 0 h10 ≫ homologyMap l 0 = 0 :=
            comp_eq_zero_transport (Cone.S₁ l (-1) 0 h10) _ _ _ _ _
              (Cone.δ_square l (-1) 0 h10) (Cone.e_naturality 0 l)
          have : Mono (homologyMap l 0) := by
            rw [hl]
            have : Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).mpr hf
            infer_instance
          have hδ : Cone.δ l (-1) 0 h10 = 0 := zero_of_comp_mono _ hcomp
          rw [IsZero.iff_id_eq_zero, ← cancel_mono (Cone.δ l (-1) 0 h10),
            Category.id_comp, zero_comp, hδ]
        · exact (Cone.exact₃ l i (i + 1) rfl).isZero_of_both_isZero
            (hL.isZero_homology i hi) (hK.isZero_homology _ (by omega))
      homologyZeroIso := (hK.coneHomologyZeroEquiv hL f g l hl hg he).toModuleIso }

end IsResolutionOf
end SerrePositivity
