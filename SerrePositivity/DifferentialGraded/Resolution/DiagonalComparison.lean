module
public import SerrePositivity.DifferentialGraded.Resolution.CompositionChange
public import SerrePositivity.DifferentialGraded.Derived.DiagonalRestriction

/-! # 指定dg圏解像度の既存の変更同値による対角bimoduleの保存 -/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory BimoduleTensor
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 共通比較sourceの対角を、既存の導来bimodule圏の対象として読む。 -/
def comparisonDiagonal (P : KFlatDGResolution.{u, v, w} A D) :
    DerivedBimoduleCategory A P.ComparisonSource P.ComparisonSource :=
  (bimoduleToDerived A P.ComparisonSource P.ComparisonSource).obj
    (rightKFlatDiagonal A P.ComparisonSource).obj

/-- 指定解像度から共通sourceへの既存の比較左脚は、対角を同型で保存する。 -/
def comparisonLeftDiagonalIso (P : KFlatDGResolution.{u, v, w} A D) :
    (comparisonLeft A P P).obj (diagonal A P) ≅ comparisonDiagonal A P :=
  (derivedDiagonalRestrictionIso A P.ComparisonSource P.source P.comparisonLeft
    P.comparisonLeft_quasiEquivalence.1).symm

variable [Small.{u} D]

/-- 標準解像度から共通sourceへの既存の比較右脚も、対角を同型で保存する。 -/
def comparisonRightDiagonalIso (P : KFlatDGResolution.{u, v, w} A D) :
    (comparisonRight A P P).obj (diagonal A (KFlatDGResolution.canonical A D)) ≅
      comparisonDiagonal A P :=
  (derivedDiagonalRestrictionIso A P.ComparisonSource (KFlatDGResolution.canonical A D).source
    P.comparisonRight P.comparisonRight_quasiEquivalence.1).symm

/-- 既存の標準解像度比較同値は、指定対角を標準対角へ送る。 -/
def canonicalComparisonDiagonalIso (P : KFlatDGResolution.{u, v, w} A D) :
    (canonicalComparisonEquivalence A P P).functor.obj (diagonal A P) ≅
      diagonal A (KFlatDGResolution.canonical A D) :=
  (comparisonRightEquivalence A P P).inverse.mapIso
      (comparisonLeftDiagonalIso A P ≪≫ (comparisonRightDiagonalIso A P).symm) ≪≫
    ((comparisonRightEquivalence A P P).unitIso.app
      (diagonal A (KFlatDGResolution.canonical A D))).symm

/-- 両端の指定解像度を同時に変更する既存の同値は、対角bimoduleを保存する。 -/
def changeDiagonalIso (P : KFlatDGResolution.{u, v, w} A D)
    (Q : KFlatDGResolution.{u, v, z} A D) :
    (changeEquivalence A P P Q Q).functor.obj (diagonal A P) ≅ diagonal A Q :=
  (canonicalComparisonEquivalence A Q Q).inverse.mapIso
      (canonicalComparisonDiagonalIso A P ≪≫ (canonicalComparisonDiagonalIso A Q).symm) ≪≫
    ((canonicalComparisonEquivalence A Q Q).unitIso.app (diagonal A Q)).symm

end SerrePositivity.DifferentialGraded.ResolutionBimodule
