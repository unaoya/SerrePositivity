module
public import SerrePositivity.KTheory.ComparisonInverse
public import SerrePositivity.KTheory.LocalizationCoefficients

/-! # Naturality of the supported K₀/G₀ comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
variable {R S : Type u} [CommRing R] [CommRing S]

namespace PerfectModuleResolution
/-- Flat base change of any strictly perfect module resolution. -/
def baseChange (φ : R →+* S) (hf : φ.Flat) {M : ModuleCat.{u} R}
    (F : PerfectModuleResolution M) :
    PerfectModuleResolution ((ModuleCat.extendScalars φ).obj M) := by
  algebraize [φ]
  have : Module.Flat R S := hf
  let hS := isResolutionOf_baseChange_of_flat R S M F.resolution
  let e := moduleCatBaseChangeTensorEquiv (R := R) (B := S) M
  refine ⟨SerrePositivity.baseChange φ F.complex, ?_,
    strictlyPerfectComplex_baseChange φ F.complex F.perfect⟩
  exact { hS with homologyZeroIso := hS.homologyZeroIso ≪≫ e.symm.toModuleIso }
end PerfectModuleResolution


/-- The proved finite-projective resolution contract is stable under any localization. -/
lemma hasFiniteProjectiveResolutions_of_localization [Algebra R S]
    (P : Submonoid R) [IsLocalization P S] [IsNoetherianRing R]
    [HasFiniteProjectiveResolutions R] : HasFiniteProjectiveResolutions S where
  exists_resolution M h := by
    have := h
    obtain ⟨M₀, hfinite, _, ⟨e⟩⟩ := exists_finitePresentation_descent P M
    have := hfinite
    obtain ⟨F, ⟨hF⟩, hp⟩ := HasFiniteProjectiveResolutions.exists_resolution M₀
    let G := PerfectModuleResolution.baseChange (algebraMap R S)
      (by rw [RingHom.flat_algebraMap_iff]; exact IsLocalization.flat S P)
      (⟨F, hF, hp⟩ : PerfectModuleResolution M₀)
    let e' := (moduleCatBaseChangeTensorEquiv (R := R) (B := S) M₀).trans e
    exact ⟨G.complex, ⟨{G.resolution with
      homologyZeroIso := G.resolution.homologyZeroIso ≪≫ e'.toModuleIso}⟩, G.perfect⟩

variable [IsNoetherianRing R] [IsNoetherianRing S]
  [HasFiniteProjectiveResolutions R] [HasFiniteProjectiveResolutions S]

omit [IsNoetherianRing R] in
lemma resClass_enlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W)
    (M : SupportedFGModuleOn Z) :
    K0WithSupport.enlarge h (resClass M) = resClass (M.enlarge h) := by
  let F := chosenPerfectModuleResolution M.obj
  rw [resClass_eq M F, resClass_eq (M.enlarge h) F]
  unfold PerfectModuleResolution.k0Class
  rw [K0WithSupport.enlarge_mk]
  apply K0WithSupport.mk_iso
  exact ObjectProperty.isoMk _ (Iso.refl _)

omit [IsNoetherianRing R] [IsNoetherianRing S] in
lemma resClass_map (φ : R →+* S) (hf : φ.Flat)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (M : SupportedFGModuleOn Z) :
    K0WithSupport.map φ Z W h (resClass M) = resClass (M.baseChange φ Z W h) := by
  let F := chosenPerfectModuleResolution M.obj
  let G := F.baseChange φ hf
  rw [resClass_eq M F, resClass_eq (M.baseChange φ Z W h) G]
  unfold PerfectModuleResolution.k0Class
  rw [K0WithSupport.map_mk]
  apply K0WithSupport.mk_iso
  exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Iso.refl _))

namespace G0WithSupport
omit [IsNoetherianRing R] in
lemma resolutionMap_enlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) :
    (K0WithSupport.enlarge h).comp (resolutionMap Z) = (resolutionMap W).comp (enlarge h) := by
  apply hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, resolutionMap_mk, enlarge_mk]
  exact resClass_enlarge h M

omit [IsNoetherianRing R] [IsNoetherianRing S] in
lemma resolutionMap_map (φ : R →+* S) (hf : φ.Flat)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W) :
    (K0WithSupport.map φ Z W h).comp (resolutionMap Z) =
      (resolutionMap W).comp (map φ hf Z W h) := by
  apply hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, resolutionMap_mk, map_mk]
  exact resClass_map φ hf Z W h M
end G0WithSupport

namespace K0WithSupport
lemma homologyEuler_enlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) :
    (homologyEuler W).comp (enlarge h) = (G0WithSupport.enlarge h).comp (homologyEuler Z) := by
  have hres := G0WithSupport.resolutionMap_enlarge h
  have h := congrArg (fun f => ((homologyEuler W).comp f).comp (homologyEuler Z)) hres
  simp only [AddMonoidHom.comp_assoc, resolutionMap_homologyEuler, AddMonoidHom.comp_id] at h
  rw [← AddMonoidHom.comp_assoc, homologyEuler_resolutionMap, AddMonoidHom.id_comp] at h
  exact h

lemma homologyEuler_map (φ : R →+* S) (hf : φ.Flat)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W) :
    (homologyEuler W).comp (map φ Z W h) =
      (G0WithSupport.map φ hf Z W h).comp (homologyEuler Z) := by
  have hres := G0WithSupport.resolutionMap_map φ hf Z W h
  have hc := congrArg (fun f => ((homologyEuler W).comp f).comp (homologyEuler Z)) hres
  simp only [AddMonoidHom.comp_assoc, resolutionMap_homologyEuler, AddMonoidHom.comp_id] at hc
  rw [← AddMonoidHom.comp_assoc, homologyEuler_resolutionMap, AddMonoidHom.id_comp] at hc
  exact hc
end K0WithSupport
end SerrePositivity
