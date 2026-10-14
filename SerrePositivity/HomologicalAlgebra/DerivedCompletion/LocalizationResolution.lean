module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.LocalizationPresentation
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleResolution
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # 局所化の二項自由分解と完備複体へのHom

自由telescopeの短完全列を実際の二項複体にし、K射影性と標準増大射を証明する。
完備性の定義に現れる全次数の射は、この分解からの線形Hom複体のコホモロジーと一致する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 局所化の自由presentationを零次数複体の短完全列へ移したもの。 -/
def localizationPresentationComplex (a : R) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (localizationPresentation R a).map (CochainComplex.singleFunctor (ModuleCat R) 0)

/-- 零次数複体へ移しても局所化のpresentationは短完全。 -/
theorem localizationPresentationComplex_shortExact (a : R) :
    (localizationPresentationComplex R a).ShortExact :=
  (localizationPresentation_shortExact R a).map_of_exact _

/-- 主元局所化の、自由telescopeの差分の錐による二項分解。 -/
def localizationResolutionComplex (a : R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.mappingCone (localizationPresentationComplex R a).f

/-- 二項分解は正次数で零。 -/
instance localizationResolutionComplex_isStrictlyLE (a : R) :
    (localizationResolutionComplex R a).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [localizationResolutionComplex, CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨HomologicalComplex.isZero_single_obj_X _ 0 _ (i + 1) (by omega),
    HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩

/-- 二項分解の各項は射影的。 -/
instance localizationResolutionComplex_projective (a : R) (i : ℤ) :
    Projective ((localizationResolutionComplex R a).X i) := by
  have : Projective (((localizationPresentationComplex R a).X₁).X (i + 1)) := by
    change Projective (((CochainComplex.singleFunctor (ModuleCat R) 0).obj
      (localizationPresentation R a).X₁).X (i + 1))
    infer_instance
  have : Projective (((localizationPresentationComplex R a).X₂).X i) := by
    change Projective (((CochainComplex.singleFunctor (ModuleCat R) 0).obj
      (localizationPresentation R a).X₂).X i)
    infer_instance
  exact Projective.of_iso
    (homotopyCofiber.XIsoBiprod (localizationPresentationComplex R a).f i (i + 1) rfl).symm
    inferInstance

/-- 局所化の二項自由分解はK射影的。 -/
instance localizationResolutionComplex_isKProjective (a : R) :
    (localizationResolutionComplex R a).IsKProjective :=
  CochainComplex.isKProjective_of_projective _ 0

/-- 二項自由分解の、局所化を零次数に置く複体への標準増大射。 -/
def localizationResolutionAugmentation (a : R) :
    localizationResolutionComplex R a ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (Localization.Away a)) :=
  CochainComplex.mappingCone.descShortComplex (localizationPresentationComplex R a)

/-- 標準増大射は準同型同値。 -/
instance localizationResolutionAugmentation_quasiIso (a : R) :
    QuasiIso (localizationResolutionAugmentation R a) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex
    (localizationPresentationComplex_shortExact R a)

/-- 二項自由分解の実導来像は、標準の局所化対象に一致する。 -/
def localizationResolutionDerivedIso (a : R) :
    DerivedCategory.Q.obj (localizationResolutionComplex R a) ≅ localizationObject R a :=
  asIso (DerivedCategory.Q.map (localizationResolutionAugmentation R a))

/-- 二項自由分解からのHom複体のコホモロジーは、局所化対象からの導来射に一致する。 -/
def localizationResolutionHomologyEquiv (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (CochainComplex.linearHomComplex R (localizationResolutionComplex R a) K).homology i ≃
      ShiftedHom (localizationObject R a) (DerivedCategory.Q.obj K) i := by
  letI : HasSmallLocalizedShiftedHom.{u + 1}
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) ℤ
      (localizationResolutionComplex R a) K := fun m n ↦
    hasSmallLocalizedHom_of_isLocalization
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (DerivedCategory.Q (C := ModuleCat R))
      (X := (localizationResolutionComplex R a)⟦m⟧) (Y := K⟦n⟧)
  exact (CochainComplex.HomComplex.homologyLinearEquiv R _ K i).toEquiv |>.trans
    ((CochainComplex.HomComplex.CohomologyClass.equivOfIsKProjective.{u + 1}
      (K := localizationResolutionComplex R a) (L := K) (n := i)).trans
      ((SmallShiftedHom.equiv _ DerivedCategory.Q).trans
        (Iso.homCongr (localizationResolutionDerivedIso R a) (Iso.refl _))))

/-- 完備複体への線形Hom複体のコホモロジーは全次数で零。 -/
theorem localizationResolutionHomology_subsingleton (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) (i : ℤ) :
    Subsingleton
      ((CochainComplex.linearHomComplex R (localizationResolutionComplex R a) K).homology i) := by
  let : Subsingleton (ShiftedHom (localizationObject R a) (DerivedCategory.Q.obj K) i) :=
    ⟨fun x y ↦ (hK i x).trans (hK i y).symm⟩
  exact (localizationResolutionHomologyEquiv R a K i).injective.subsingleton

/-- 完備性は、二項自由分解からの線形Hom複体の全コホモロジーの消滅と同値。 -/
theorem isComplete_iff_localizationResolutionHomology_subsingleton (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsComplete R a (DerivedCategory.Q.obj K) ↔
      ∀ i : ℤ, Subsingleton
        ((CochainComplex.linearHomComplex R (localizationResolutionComplex R a) K).homology i) := by
  constructor
  · exact localizationResolutionHomology_subsingleton R a K
  · intro h i x
    let := h i
    have : Subsingleton (ShiftedHom (localizationObject R a) (DerivedCategory.Q.obj K) i) :=
      (localizationResolutionHomologyEquiv R a K i).symm.injective.subsingleton
    exact Subsingleton.elim _ _

/-- 完備性の定義と、具体的な線形Hom複体の非輪状性の比較。 -/
theorem isComplete_iff_localizationResolutionHom_acyclic (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsComplete R a (DerivedCategory.Q.obj K) ↔
      (CochainComplex.linearHomComplex R (localizationResolutionComplex R a) K).Acyclic := by
  rw [isComplete_iff_localizationResolutionHomology_subsingleton, acyclic_iff]
  apply forall_congr'
  intro i
  rw [exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]

end SerrePositivity.DerivedCompletion
