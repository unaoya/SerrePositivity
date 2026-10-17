module
public import SerrePositivity.DifferentialGraded.Resolution.CanonicalZigzag
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleFullComposition

/-! # dg圏解像度比較の両脚に沿う全導来bimodule合成比較 -/
@[expose] public section
noncomputable section
universe u v w z t w'
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  {C : Type w} [DGCategory A C]
  (L : Type z) [DGCategory A L] [Small.{u} L] (hL : localHomKFlat A L)

/-- 指定解像度側から共通比較sourceへ中間圏を制限した合成の比較。 -/
def middleComparisonLeftIso (P : KFlatDGResolution.{u, w, w'} A C) :
    middleRestrictionDerivedSource A B P.source P.ComparisonSource L P.comparisonLeft hL ≅
      derivedBimoduleComposeFunctor A B P.source L hL :=
  derivedMiddleRestrictionIso A B P.source P.ComparisonSource L P.comparisonLeft
    P.comparisonLeft_quasiEquivalence hL

/-- 共通sourceをさらに準同値で細分しても、既存の一段階比較と二段階比較が一致する。 -/
lemma middleComparisonLeftIso_refine (P : KFlatDGResolution.{u, w, w'} A C)
    (S : Type t) [DGCategory A S] [Small.{u} S]
    (H : DGFunctor A S P.ComparisonSource) (hH : QuasiEquivalence H) :
    middleIteratedDerivedSourceIso A B S P.ComparisonSource P.source L H P.comparisonLeft hL ≪≫
        derivedMiddleRestrictionIso A B P.source S L (H.comp P.comparisonLeft)
          (quasiEquivalence_comp H P.comparisonLeft hH P.comparisonLeft_quasiEquivalence) hL =
      middleIteratedDerivedIso A B S P.ComparisonSource P.source L H P.comparisonLeft hL
        hH P.comparisonLeft_quasiEquivalence :=
  derivedMiddleRestrictionIso_functor_comp A B S P.ComparisonSource P.source L
    H P.comparisonLeft hL hH P.comparisonLeft_quasiEquivalence

variable [Small.{u} C]

/-- 標準解像度側から同じ共通sourceへ中間圏を制限した合成の比較。 -/
def middleComparisonRightIso (P : KFlatDGResolution.{u, w, w'} A C) :
    middleRestrictionDerivedSource A B (KFlatDGResolution.canonical A C).source
        P.ComparisonSource L P.comparisonRight hL ≅
      derivedBimoduleComposeFunctor A B (KFlatDGResolution.canonical A C).source L hL :=
  derivedMiddleRestrictionIso A B (KFlatDGResolution.canonical A C).source
    P.ComparisonSource L P.comparisonRight P.comparisonRight_quasiEquivalence hL

lemma middleComparisonRightIso_refine (P : KFlatDGResolution.{u, w, w'} A C)
    (S : Type t) [DGCategory A S] [Small.{u} S]
    (H : DGFunctor A S P.ComparisonSource) (hH : QuasiEquivalence H) :
    middleIteratedDerivedSourceIso A B S P.ComparisonSource
        (KFlatDGResolution.canonical A C).source L H P.comparisonRight hL ≪≫
        derivedMiddleRestrictionIso A B (KFlatDGResolution.canonical A C).source S L
          (H.comp P.comparisonRight)
          (quasiEquivalence_comp H P.comparisonRight hH P.comparisonRight_quasiEquivalence) hL =
      middleIteratedDerivedIso A B S P.ComparisonSource
        (KFlatDGResolution.canonical A C).source L H P.comparisonRight hL
        hH P.comparisonRight_quasiEquivalence :=
  derivedMiddleRestrictionIso_functor_comp A B S P.ComparisonSource
    (KFlatDGResolution.canonical A C).source L H P.comparisonRight hL
    hH P.comparisonRight_quasiEquivalence

end SerrePositivity.DifferentialGraded.ResolutionBimodule
