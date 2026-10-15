module
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyZeroTorsion
public import SerrePositivity.HomologicalAlgebra.IdealPowerTorsionBaseChange

/-! # Actual zero local cohomology under coefficient-ring and support changes -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R D : Type u} [CommRing R] [CommRing D]
variable [IsNoetherianRing R] [IsNoetherianRing D]

/-- Actual Mathlib zero local cohomology is independent of the coefficient ring and support
under the indicated radical equality. No flatness or regularity is assumed. -/
def localCohomologyZeroRestrictScalarsNatIso (φ : R →+* D)
    {e r : ℕ} (z : Fin e → R) (y : Fin r → D)
    (h : ((Ideal.span (Set.range z)).map φ).radical = (Ideal.span (Set.range y)).radical) :
    ModuleCat.restrictScalars φ ⋙ localCohomology (Ideal.span (Set.range z)) 0 ≅
      localCohomology (Ideal.span (Set.range y)) 0 ⋙ ModuleCat.restrictScalars φ :=
  Functor.isoWhiskerLeft (ModuleCat.restrictScalars φ) (localCohomologyZeroPowerTorsionNatIso z) ≪≫
    idealPowerTorsionRestrictScalarsSupportNatIso φ
      (Ideal.span (Set.range z)) (Ideal.span (Set.range y)) h ≪≫
    Functor.isoWhiskerRight (localCohomologyZeroPowerTorsionNatIso y).symm
      (ModuleCat.restrictScalars φ)

/-- The actual comparison preserves and reflects zero induced coefficient maps. -/
lemma localCohomologyZeroRestrictScalars_map_eq_zero_iff (φ : R →+* D)
    {e r : ℕ} (z : Fin e → R) (y : Fin r → D)
    (h : ((Ideal.span (Set.range z)).map φ).radical = (Ideal.span (Set.range y)).radical)
    {M N : ModuleCat.{u} D} (f : M ⟶ N) :
    (localCohomology (Ideal.span (Set.range z)) 0).map
        ((ModuleCat.restrictScalars φ).map f) = 0 ↔
      (localCohomology (Ideal.span (Set.range y)) 0).map f = 0 := by
  let E := localCohomologyZeroRestrictScalarsNatIso φ z y h
  have hn := E.hom.naturality f
  constructor
  · intro hf
    have hz : (ModuleCat.restrictScalars φ).map
        ((localCohomology (Ideal.span (Set.range y)) 0).map f) = 0 := by
      apply (cancel_epi (E.app M).hom).mp
      simpa only [Functor.comp_map, Functor.comp_obj, Iso.app_hom, hf, zero_comp, comp_zero]
        using hn.symm
    exact ((ModuleCat.restrictScalars φ).map_eq_zero_iff).mp hz
  · intro hf
    apply (cancel_mono (E.app N).hom).mp
    simpa only [Functor.comp_map, Functor.comp_obj, Iso.app_hom, hf, Functor.map_zero,
      zero_comp, comp_zero] using hn

end SerrePositivity
