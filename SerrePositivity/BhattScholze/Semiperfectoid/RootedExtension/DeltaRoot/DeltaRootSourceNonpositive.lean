module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootSourceRawComparison
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive

/-! # 元の実根添加源の非正性と同じ係数制限augmentationのH0同型 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "α" => deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d)
local notation "β" => deltaDivisionSourceEval E r
local notation "Mβ" => baseChangeScalarModule β
local notation "Mα" => baseChangeScalarModule α
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedTensor
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "C₀" => algebraMap A L

set_option maxHeartbeats 800000 in
-- Retain the original scalar actions while comparing explicit nonpositive projective tensor models.
/-- 同じ元の実A対象は非正次数の対象であり、離散性や完備性は仮定しない。 -/
theorem deltaRootSourceCoefficient_isLE_zero :
    (DeltaRootSourceCoefficientObject d D b).obj.IsLE 0 := by
  let Pβ := projectiveResolutionDerivedModel (projectiveResolution Mβ)
  let Pα := projectiveResolutionDerivedModel (projectiveResolution Mα)
  let K := cochainTensor Pβ.complex Pα.complex
  let KR : CochainComplex (ModuleCat A) ℤ :=
    ((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj K
  have hβ : Pβ.complex.IsStrictlyLE 0 := Pβ.bounded
  have hα : Pα.complex.IsStrictlyLE 0 := Pα.bounded
  have hK : K.IsStrictlyLE 0 := by
    simpa only [add_zero] using cochainTensor_isStrictlyLE Pβ.complex Pα.complex 0 0
  have hKR : KR.IsStrictlyLE 0 := by
    apply (CochainComplex.isStrictlyLE_iff _ _).mpr
    intro i hi
    change IsZero ((ModuleCat.restrictScalars C₀).obj (K.X i))
    exact (ModuleCat.restrictScalars C₀).map_isZero (K.isZero_of_isStrictlyLE 0 i hi)
  let e : (DeltaRootSourceCoefficientObject d D b).obj ≅ DerivedCategory.Q.obj KR :=
    (derivedRestrictScalars C₀).mapIso
        (boundedAboveDerivedTensorModelIso
          (boundedAboveDerivedSingleFunctor.obj Mβ)
          (boundedAboveDerivedSingleFunctor.obj Mα) Pβ Pα) ≪≫
      (derivedRestrictScalarsFactors C₀).app K
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0

/-- 元Aへ制限した同じ実二因子源は、全正次数でホモロジーが消える。 -/
theorem deltaRootSourceCoefficient_homology_isZero_positive (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      (DeltaRootSourceCoefficientObject d D b).obj) :=
  (DerivedCategory.isLE_iff _ _).mp (deltaRootSourceCoefficient_isLE_zero D d b) i hi

/-- 同じaugmentationの終域である係数制限raw singleも非正次数である。 -/
theorem deltaRootSourceRawCoefficient_isLE_zero :
    (DeltaRootSourceRawCoefficientObject D d b).obj.IsLE 0 := by
  let e : (DeltaRootSourceRawCoefficientObject D d b).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat A) 0).obj
        ((ModuleCat.restrictScalars C₀).obj (DeltaRootSourceRawModule D d b)) :=
    (derivedRestrictScalarsSingleIso C₀ 0).app (DeltaRootSourceRawModule D d b)
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0

/-- 元Aへ制限した標準augmentationそのものも、H0に同型を誘導する。 -/
theorem deltaRootSourceRawCoefficientAugmentation_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) 0).map
      (deltaRootSourceRawCoefficientAugmentation D d b).hom) := by
  let f := (deltaRootSourceRawAugmentation D d b).hom
  let H := DerivedCategory.homologyFunctor (ModuleCat A) 0
  let e := derivedRestrictScalarsHomologyIso C₀ 0
  have hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map f) :=
    deltaRootSourceRawAugmentation_h0_isIso D d b
  have hn := e.hom.naturality f
  simp only [Functor.comp_map] at hn
  have he : IsIso (H.map ((derivedRestrictScalars C₀).map f) ≫ e.hom.app _) := by
    rw [hn]
    infer_instance
  change IsIso (H.map ((derivedRestrictScalars C₀).map f))
  exact IsIso.of_isIso_comp_right _ (e.hom.app _)

end SerrePositivity.BhattScholze
