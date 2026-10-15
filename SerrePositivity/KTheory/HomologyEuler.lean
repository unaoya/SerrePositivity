module
public import SerrePositivity.KTheory.HomologyEulerBasic
public import SerrePositivity.KTheory.ResolutionAdditivity

/-! # Homology Euler classes of supported resolutions -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits Pretriangulated
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

namespace K0WithSupport
lemma homologyEuler_resolution (M : SupportedFGModuleOn Z) (F : PerfectModuleResolution M.obj) :
    homologyEuler Z (F.k0Class Z M.property.2) = G0WithSupport.mk M := by
  rw [PerfectModuleResolution.k0Class, homologyEuler_mk]
  unfold supportedHomologyEuler supportedModuleEuler
  rw [finsum_eq_single _ (0 : ℤ)]
  · simp only [Int.negOnePow_zero, Units.val_one, one_smul]
    apply G0WithSupport.mk_iso
    exact (HomotopyCategory.homologyFunctorFactors _ _ 0).app F.complex ≪≫
      F.resolution.homologyZeroIso
  · intro q hq
    rw [G0WithSupport.mk_of_isZero _ ?_, smul_zero]
    exact (F.resolution.isZero_homology q hq).of_iso
      ((HomotopyCategory.homologyFunctorFactors _ _ q).app F.complex)

variable [HasFiniteProjectiveResolutions R]
lemma homologyEuler_resolutionMap : (homologyEuler Z).comp (G0WithSupport.resolutionMap Z) =
    AddMonoidHom.id (G0WithSupport Z) := by
  apply G0WithSupport.hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, G0WithSupport.resolutionMap_mk, AddMonoidHom.id_apply]
  exact homologyEuler_resolution Z M (chosenPerfectModuleResolution M.obj)
end K0WithSupport
end SerrePositivity
