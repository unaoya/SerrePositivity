module
public import SerrePositivity.KTheory.G0Localization
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.PerfectComplex.FiniteProjectiveResolutions
public import SerrePositivity.HomologicalAlgebra.KProjectiveLift
public import SerrePositivity.CategoryTheory.TriangulatedK0

/-! # The supported K₀ class of a module resolution -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- A chosen strictly perfect module resolution. -/
structure PerfectModuleResolution (M : ModuleCat.{u} R) where
  complex : CochainComplex (ModuleCat.{u} R) ℤ
  resolution : IsResolutionOf complex M
  perfect : strictlyPerfectComplex R complex



namespace K0WithSupport
lemma mk_shift (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (X : SupportedPerfectHomotopyOn Z) (n : ℤ) :
    mk Z (X⟦n⟧) = ((n.negOnePow : ℤˣ) : ℤ) • mk Z X := TriangulatedK0.mk_shift X n
end K0WithSupport

namespace PerfectModuleResolution
variable {M N : ModuleCat.{u} R}
/-- The augmentation to the module placed in degree zero. -/
def augmentation (F : PerfectModuleResolution M) :
    F.complex ⟶ (HomologicalComplex.single _ (.up ℤ) 0).obj M :=
  toSingleOfHomology F.complex (d_zero_one_eq_zero _ F.resolution.isZero_X)
    F.resolution.homologyZeroIso.hom

instance augmentation_quasiIso (F : PerfectModuleResolution M) : QuasiIso F.augmentation :=
  quasiIso_toSingleOfHomology _ _ _ F.resolution.isZero_homology

/-- A module map lifts between perfect resolutions, inducing the specified map on H⁰. -/
lemma exists_comparison (F : PerfectModuleResolution M) (G : PerfectModuleResolution N)
    (g : M ⟶ N) :
    ∃ f : F.complex ⟶ G.complex,
      homologyMap f 0 ≫ G.resolution.homologyZeroIso.hom =
        F.resolution.homologyZeroIso.hom ≫ g := by
  have : F.complex.IsKProjective := strictlyPerfectComplex_isKProjective F.perfect
  let ε := F.resolution.homologyZeroIso.hom ≫ g
  let a := toSingleOfHomology F.complex (d_zero_one_eq_zero _ F.resolution.isZero_X) ε
  obtain ⟨f, ⟨H⟩⟩ := exists_lift_of_quasiIso G.augmentation a
  refine ⟨f, ?_⟩
  have hF := toSingleOfHomology_homologyMap F.complex
    (d_zero_one_eq_zero _ F.resolution.isZero_X) ε
  have hG := toSingleOfHomology_homologyMap G.complex
    (d_zero_one_eq_zero _ G.resolution.isZero_X) G.resolution.homologyZeroIso.hom
  have hh : homologyMap f 0 ≫ homologyMap G.augmentation 0 = homologyMap a 0 := by
    rw [← homologyMap_comp]
    exact H.homologyMap_eq 0
  calc
    homologyMap f 0 ≫ G.resolution.homologyZeroIso.hom =
        homologyMap f 0 ≫ homologyMap G.augmentation 0 ≫
          (HomologicalComplex.singleObjHomologySelfIso _ 0 N).hom := by
      simpa only [augmentation, Category.assoc] using
        congrArg (fun k => homologyMap f 0 ≫ k) hG.symm
    _ = homologyMap a 0 ≫ (HomologicalComplex.singleObjHomologySelfIso _ 0 N).hom := by
      rw [← Category.assoc, hh]
    _ = F.resolution.homologyZeroIso.hom ≫ g := hF

lemma comparison_quasiIso (F : PerfectModuleResolution M) (G : PerfectModuleResolution N)
    (e : M ≅ N) (f : F.complex ⟶ G.complex)
    (hf : homologyMap f 0 ≫ G.resolution.homologyZeroIso.hom =
      F.resolution.homologyZeroIso.hom ≫ e.hom) : QuasiIso f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hi : i = 0
  · subst i
    have h : homologyMap f 0 = F.resolution.homologyZeroIso.hom ≫ e.hom ≫
        G.resolution.homologyZeroIso.inv := by
      rw [← Category.assoc, Iso.eq_comp_inv]
      exact hf
    rw [h]
    infer_instance
  · exact ⟨0, (F.resolution.isZero_homology i hi).eq_of_src _ _,
      (G.resolution.isZero_homology i hi).eq_of_src _ _⟩


/-- Isomorphic modules have homotopy equivalent strictly perfect resolutions. -/
lemma exists_homotopyEquiv (F : PerfectModuleResolution M) (G : PerfectModuleResolution N)
    (e : M ≅ N) : Nonempty (HomotopyEquiv F.complex G.complex) := by
  obtain ⟨f, hf⟩ := F.exists_comparison G e.hom
  have hq := F.comparison_quasiIso G e f hf
  obtain ⟨h, _⟩ := (strictlyPerfectComplex_quasiIso_iff F.perfect G.perfect f).mp hq
  exact ⟨h⟩

lemma support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (F : PerfectModuleResolution M) (hM : Module.support R M ⊆ Z) :
    HasHomologySupportOn Z F.complex := by
  intro i
  by_cases hi : i = 0
  · subst i
    rw [F.resolution.homologyZeroIso.toLinearEquiv.support_eq]
    exact hM
  · have : Subsingleton (F.complex.homology i) :=
      ModuleCat.subsingleton_of_isZero (F.resolution.isZero_homology i hi)
    simp [Module.support_eq_empty]

/-- The class obtained from any chosen perfect resolution. -/
def k0Class (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (F : PerfectModuleResolution M)
    (hM : Module.support R M ⊆ Z) : K0WithSupport Z :=
  K0WithSupport.mk Z (supportedPerfectOnObj Z F.complex F.perfect (F.support hM))

lemma class_eq_of_iso (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (F : PerfectModuleResolution M) (G : PerfectModuleResolution N)
    (hM : Module.support R M ⊆ Z) (hN : Module.support R N ⊆ Z) (e : M ≅ N) :
    F.k0Class Z hM = G.k0Class Z hN := by
  obtain ⟨f, hf⟩ := F.exists_comparison G e.hom
  have : QuasiIso f := F.comparison_quasiIso G e f hf
  exact K0WithSupport.mk_eq_of_quasiIso Z _ _ F.perfect G.perfect (F.support hM) (G.support hN) f
end PerfectModuleResolution

variable [HasFiniteProjectiveResolutions R]
/-- Choose a perfect resolution using the proved resolution-existence contract. -/
def chosenPerfectModuleResolution (M : ModuleCat.{u} R) [Module.Finite R M] :
    PerfectModuleResolution M := by
  let h := HasFiniteProjectiveResolutions.exists_resolution M
  let F := Classical.choose h
  have hF := Classical.choose_spec h
  exact ⟨F, Classical.choice hF.1, hF.2⟩

/-- The resolution class, independent of the resolution chosen in its construction. -/
def resClass {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} (M : SupportedFGModuleOn Z) :
    K0WithSupport Z := (chosenPerfectModuleResolution M.obj).k0Class Z M.property.2

lemma resClass_eq {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} (M : SupportedFGModuleOn Z)
    (F : PerfectModuleResolution M.obj) : resClass M = F.k0Class Z M.property.2 :=
  (chosenPerfectModuleResolution M.obj).class_eq_of_iso Z F M.property.2 M.property.2 (Iso.refl _)

lemma resClass_iso {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {M N : SupportedFGModuleOn Z} (e : M.obj ≅ N.obj) : resClass M = resClass N :=
  (chosenPerfectModuleResolution M.obj).class_eq_of_iso Z (chosenPerfectModuleResolution N.obj)
    M.property.2 N.property.2 e
end SerrePositivity
