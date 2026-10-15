module
public import SerrePositivity.HomologicalAlgebra.KoszulDualBaseChange
public import SerrePositivity.HomologicalAlgebra.GeneralKoszulLocalCohomology

/-! # Actual local cohomology under arbitrary Noetherian coefficient-ring changes -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R S : Type u} [CommRing R] [CommRing S]
variable {e : ℕ} (z : Fin e → R)

section Algebra
variable [Algebra R S]

local instance : Functor.PreservesHomology
    ((Functor.whiskeringRight (ModuleCat.{u} S) (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
      (ModuleCat.restrictScalars (algebraMap R S))) where
  preservesKernels f := by infer_instance
  preservesCokernels f := by infer_instance

/-- Restriction compares actual coefficient-algebra colimit homology with
the original Koszul homology functor, before any local cohomology computation. -/
def algebraKoszulColimitHomologyRestrictNatIso (i : ℕ) :
    (algebraKoszulDualColimitComplex (C := S) z).homology i ⋙
        ModuleCat.restrictScalars (algebraMap R S) ≅
      ModuleCat.restrictScalars (algebraMap R S) ⋙ (koszulDualColimitComplex z).homology i :=
  (((algebraKoszulDualColimitComplex (C := S) z).sc i).mapHomologyIso
    ((Functor.whiskeringRight (ModuleCat.{u} S) (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
      (ModuleCat.restrictScalars (algebraMap R S)))).symm ≪≫
    (homologyFunctor (ModuleCat.{u} S ⥤ ModuleCat.{u} R) (.up ℕ) i).mapIso
      (algebraKoszulDualColimitRestrictIso (C := S) z) ≪≫
    ((koszulDualColimitComplex z).sc i).mapHomologyIso
      ((Functor.whiskeringLeft (ModuleCat.{u} S) (ModuleCat.{u} R) (ModuleCat.{u} R)).obj
        (ModuleCat.restrictScalars (algebraMap R S)))

/-- Arbitrary finite sequences compute local cohomology with its actual
coefficient-algebra action after restriction, without a regularity assumption. -/
def generalAlgebraKoszulColimitLocalCohomologyNatIso [IsNoetherianRing R] (i : ℕ) :
    (algebraKoszulDualColimitComplex (C := S) z).homology i ⋙
        ModuleCat.restrictScalars (algebraMap R S) ≅
      ModuleCat.restrictScalars (algebraMap R S) ⋙
        localCohomology (Ideal.span (Set.range z)) i :=
  algebraKoszulColimitHomologyRestrictNatIso z i ≪≫
    Functor.isoWhiskerLeft (ModuleCat.restrictScalars (algebraMap R S))
      ((asFunctorCochainHomologyIso (koszulDualColimitComplex z) i).symm ≪≫
        generalKoszulLocalCohomologyComparison z i)

/-- Actual local cohomology is independent of the coefficient ring, with
support extended along the ring map. No flatness is required. -/
def localCohomologyAlgebraRestrictScalarsNatIso
    [IsNoetherianRing R] [IsNoetherianRing S] (i : ℕ) :
    ModuleCat.restrictScalars (algebraMap R S) ⋙
        localCohomology (Ideal.span (Set.range z)) i ≅
      localCohomology (Ideal.span (Set.range ((algebraMap R S) ∘ z))) i ⋙
        ModuleCat.restrictScalars (algebraMap R S) :=
  (generalAlgebraKoszulColimitLocalCohomologyNatIso (S := S) z i).symm ≪≫
    Functor.isoWhiskerRight
      ((homologyFunctor (ModuleCat.{u} S ⥤ ModuleCat.{u} S) (.up ℕ) i).mapIso
        (koszulDualColimitBaseChangeIso (S := S) z).symm)
      (ModuleCat.restrictScalars (algebraMap R S)) ≪≫
    Functor.isoWhiskerRight
      ((asFunctorCochainHomologyIso
        (koszulDualColimitComplex ((algebraMap R S) ∘ z)) i).symm ≪≫
          generalKoszulLocalCohomologyComparison ((algebraMap R S) ∘ z) i)
      (ModuleCat.restrictScalars (algebraMap R S))

end Algebra

/-- Ring-homomorphism form of actual all-degree local cohomology ring change. -/
def localCohomologyRestrictScalarsNatIso [IsNoetherianRing R] [IsNoetherianRing S]
    (φ : R →+* S) (i : ℕ) :
    ModuleCat.restrictScalars φ ⋙ localCohomology (Ideal.span (Set.range z)) i ≅
      localCohomology (Ideal.span (Set.range (φ ∘ z))) i ⋙ ModuleCat.restrictScalars φ := by
  letI := φ.toAlgebra
  exact localCohomologyAlgebraRestrictScalarsNatIso (S := S) z i

/-- Support can be replaced by any ideal with the same extended radical,
including a maximal ideal, in every degree. -/
def localCohomologyRestrictScalarsSupportNatIso [IsNoetherianRing R] [IsNoetherianRing S]
    (φ : R →+* S) (J : Ideal S)
    (h : ((Ideal.span (Set.range z)).map φ).radical = J.radical) (i : ℕ) :
    ModuleCat.restrictScalars φ ⋙ localCohomology (Ideal.span (Set.range z)) i ≅
      localCohomology J i ⋙ ModuleCat.restrictScalars φ := by
  have hspan : Ideal.span (Set.range (φ ∘ z)) = (Ideal.span (Set.range z)).map φ := by
    rw [Ideal.map_span, ← Set.range_comp]
  have h' : (Ideal.span (Set.range (φ ∘ z))).radical = J.radical := by
    rw [hspan]
    exact h
  exact localCohomologyRestrictScalarsNatIso z φ i ≪≫
    Functor.isoWhiskerRight (localCohomology.isoOfSameRadical h' i)
      (ModuleCat.restrictScalars φ)

/-- The all-degree ring/support comparison preserves and reflects zero induced
maps of arbitrary coefficient modules. -/
lemma localCohomologyRestrictScalarsSupport_map_eq_zero_iff
    [IsNoetherianRing R] [IsNoetherianRing S] (φ : R →+* S) (J : Ideal S)
    (h : ((Ideal.span (Set.range z)).map φ).radical = J.radical) (i : ℕ)
    {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    (localCohomology (Ideal.span (Set.range z)) i).map
        ((ModuleCat.restrictScalars φ).map f) = 0 ↔
      (localCohomology J i).map f = 0 := by
  let E := localCohomologyRestrictScalarsSupportNatIso z φ J h i
  have hn := E.hom.naturality f
  constructor
  · intro hf
    have hz : (ModuleCat.restrictScalars φ).map ((localCohomology J i).map f) = 0 := by
      apply (cancel_epi (E.app M).hom).mp
      simpa only [Functor.comp_map, Functor.comp_obj, Iso.app_hom, hf, zero_comp, comp_zero]
        using hn.symm
    exact ((ModuleCat.restrictScalars φ).map_eq_zero_iff).mp hz
  · intro hf
    apply (cancel_mono (E.app N).hom).mp
    simpa only [Functor.comp_map, Functor.comp_obj, Iso.app_hom, hf, Functor.map_zero,
      zero_comp, comp_zero] using hn

end SerrePositivity
