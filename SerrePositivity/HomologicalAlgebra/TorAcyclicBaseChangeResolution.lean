module
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.HomologicalAlgebra.Tor

/-! # Projective resolutions under scalar extension with vanishing higher Tor -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Tor acyclicity, rather than flatness of the coefficient ring, preserves this resolution. -/
def isResolutionOf_baseChange_of_torVanishing (M : ModuleCat.{u} R)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsResolutionOf K M)
    (hTor : scalarExtensionTorVanishing φ M) :
    IsResolutionOf (baseChange φ K) ((ModuleCat.extendScalars φ).obj M) := by
  let F := ModuleCat.extendScalars φ
  letI : F.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj φ)
  refine
    { isZero_X := fun i hi ↦ baseChange_isZero_X_of_pos φ K hK.isZero_X i hi
      projective := fun i ↦ ?_
      isZero_homology := fun i hi ↦ ?_
      homologyZeroIso := (leftDerivedIsoCochain F hK 0).symm ≪≫
        F.leftDerivedZeroIsoSelf.app M }
  · have := hK.projective i
    change Projective (F.obj (K.X i))
    infer_instance
  · by_cases hip : 0 < i
    · exact ShortComplex.isZero_homology_of_isZero_X₂ _
        (baseChange_isZero_X_of_pos φ K hK.isZero_X i hip)
    · let n := (-i).toNat
      have hn : 0 < n := by dsimp [n]; omega
      have he : i = -(n : ℤ) := by dsimp [n]; omega
      rw [he]
      have hD := (derivedModuleBaseChange_negative_homology_vanishes_iff φ M).mpr hTor n hn
      have hF : IsZero ((F.leftDerived n).obj M) :=
        ((derivedModuleBaseChangeHomologyIso φ n).app M).isZero_iff.mp hD
      exact (leftDerivedIsoCochain F hK n).isZero_iff.mp hF

end SerrePositivity
