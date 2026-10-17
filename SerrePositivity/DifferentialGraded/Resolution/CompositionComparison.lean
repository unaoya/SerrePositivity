module
public import SerrePositivity.DifferentialGraded.Resolution.Restriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleSimultaneousRestriction

/-! # 共通dg圏解像度への既存の両端制限と導来bimodule合成の比較 -/
@[expose] public section
noncomputable section
universe u v w z v' w' z'
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory CategoryTheory.Functor BimoduleTensor
variable (A : Type u) [CommRing A]
  {B : Type v} [DGCategory A B] {C : Type w} [DGCategory A C]
  {E : Type z} [DGCategory A E]

/-- 指定解像度から共通比較sourceへの三つの既存制限は、導来合成と自然に可換する。 -/
def comparisonLeftComposeIso (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E) :
    comparisonLeft A Q R ⋙
        derivedBimoduleComposeFunctor A P.ComparisonSource Q.ComparisonSource R.ComparisonSource
          R.comparisonSource_homKFlat ⋙
        (whiskeringLeft _ _ _).obj (comparisonLeft A P Q) ≅
      composeFunctor A P Q R ⋙ (whiskeringRight _ _ _).obj (comparisonLeft A P R) :=
  derivedBimoduleComposeRestrictionIso A P.source P.ComparisonSource Q.source Q.ComparisonSource
    R.source R.ComparisonSource P.comparisonLeft Q.comparisonLeft R.comparisonLeft
    R.homKFlat R.comparisonSource_homKFlat Q.comparisonLeft_quasiEquivalence

variable [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 標準解像度から同じ共通比較sourceへの三つの既存制限も、導来合成と自然に可換する。 -/
def comparisonRightComposeIso (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E) :
    comparisonRight A Q R ⋙
        derivedBimoduleComposeFunctor A P.ComparisonSource Q.ComparisonSource R.ComparisonSource
          R.comparisonSource_homKFlat ⋙
        (whiskeringLeft _ _ _).obj (comparisonRight A P Q) ≅
      composeFunctor A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C)
          (KFlatDGResolution.canonical A E) ⋙
        (whiskeringRight _ _ _).obj (comparisonRight A P R) :=
  derivedBimoduleComposeRestrictionIso A
    (KFlatDGResolution.canonical A B).source P.ComparisonSource
    (KFlatDGResolution.canonical A C).source Q.ComparisonSource
    (KFlatDGResolution.canonical A E).source R.ComparisonSource
    P.comparisonRight Q.comparisonRight R.comparisonRight
    (KFlatDGResolution.canonical A E).homKFlat R.comparisonSource_homKFlat
    Q.comparisonRight_quasiEquivalence

end SerrePositivity.DifferentialGraded.ResolutionBimodule
