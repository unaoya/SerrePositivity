module
public import SerrePositivity.DifferentialGraded.Resolution.CompositionComparison
public import SerrePositivity.DifferentialGraded.Resolution.BimoduleDerivedEquivalence

/-! # 指定dg圏解像度の変更同値と導来bimodule合成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z v' w' z' v'' w'' z''
namespace SerrePositivity.DifferentialGraded.ResolutionBimodule
open CategoryTheory CategoryTheory.Functor BimoduleTensor

/-- 三つの圏同値に沿う合成比較を、単位・余単位により逆向きの合成比較へ送る。 -/
def inverseCompositionComparison
    {C₁ : Type*} {C₂ : Type*} {C₃ : Type*} {D₁ : Type*} {D₂ : Type*} {D₃ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* D₁] [Category* D₂] [Category* D₃]
    (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂) (E₃ : C₃ ≌ D₃)
    (H₁ : C₂ ⥤ C₁ ⥤ C₃) (H₂ : D₂ ⥤ D₁ ⥤ D₃)
    (e : E₂.functor ⋙ H₂ ⋙ (whiskeringLeft _ _ _).obj E₁.functor ≅
      H₁ ⋙ (whiskeringRight _ _ _).obj E₃.functor) :
    E₂.inverse ⋙ H₁ ⋙ (whiskeringLeft _ _ _).obj E₁.inverse ≅
      H₂ ⋙ (whiskeringRight _ _ _).obj E₃.inverse :=
  Functor.isoWhiskerLeft
      (E₂.inverse ⋙ H₁ ⋙ (whiskeringLeft _ _ _).obj E₁.inverse)
      ((whiskeringRight _ _ _).mapIso E₃.unitIso) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (Functor.isoWhiskerLeft E₂.inverse e.symm)
        ((whiskeringLeft _ _ _).obj E₁.inverse))
      ((whiskeringRight _ _ _).obj E₃.inverse) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (E₂.inverse ⋙ E₂.functor ⋙ H₂)
        ((whiskeringLeft _ _ _).mapIso E₁.counitIso))
      ((whiskeringRight _ _ _).obj E₃.inverse) ≪≫
    Functor.isoWhiskerRight E₂.counitIso
      (H₂ ⋙ (whiskeringRight _ _ _).obj E₃.inverse) ≪≫
    Functor.leftUnitor _

variable (A : Type u) [CommRing A]
  {B : Type v} [DGCategory A B] [Small.{u} B]
  {C : Type w} [DGCategory A C] [Small.{u} C]
  {E : Type z} [DGCategory A E] [Small.{u} E]

/-- 共通比較sourceを通る既存の標準解像度比較同値は、導来合成を自然同型で保つ。 -/
def canonicalComparisonComposeIso (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E) :
    (canonicalComparisonEquivalence A Q R).functor ⋙
        composeFunctor A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C)
          (KFlatDGResolution.canonical A E) ⋙
        (whiskeringLeft _ _ _).obj (canonicalComparisonEquivalence A P Q).functor ≅
      composeFunctor A P Q R ⋙
        (whiskeringRight _ _ _).obj (canonicalComparisonEquivalence A P R).functor :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (comparisonLeft A Q R)
        (inverseCompositionComparison
          (comparisonRightEquivalence A P Q) (comparisonRightEquivalence A Q R)
          (comparisonRightEquivalence A P R)
          (composeFunctor A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C)
            (KFlatDGResolution.canonical A E))
          (derivedBimoduleComposeFunctor A P.ComparisonSource Q.ComparisonSource R.ComparisonSource
            R.comparisonSource_homKFlat) (comparisonRightComposeIso A P Q R)))
      ((whiskeringLeft _ _ _).obj (comparisonLeft A P Q)) ≪≫
    Functor.isoWhiskerRight (comparisonLeftComposeIso A P Q R)
      ((whiskeringRight _ _ _).obj (comparisonRightEquivalence A P R).inverse)

/-- 両端の指定解像度を同時に変える既存のchangeEquivalenceは、導来合成を自然同型で保つ。 -/
def changeComposeIso (P : KFlatDGResolution.{u, v, v'} A B)
    (Q : KFlatDGResolution.{u, w, w'} A C) (R : KFlatDGResolution.{u, z, z'} A E)
    (P' : KFlatDGResolution.{u, v, v''} A B) (Q' : KFlatDGResolution.{u, w, w''} A C)
    (R' : KFlatDGResolution.{u, z, z''} A E) :
    (changeEquivalence A Q R Q' R').functor ⋙ composeFunctor A P' Q' R' ⋙
        (whiskeringLeft _ _ _).obj (changeEquivalence A P Q P' Q').functor ≅
      composeFunctor A P Q R ⋙
        (whiskeringRight _ _ _).obj (changeEquivalence A P R P' R').functor :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (canonicalComparisonEquivalence A Q R).functor
        (inverseCompositionComparison
          (canonicalComparisonEquivalence A P' Q') (canonicalComparisonEquivalence A Q' R')
          (canonicalComparisonEquivalence A P' R') (composeFunctor A P' Q' R')
          (composeFunctor A (KFlatDGResolution.canonical A B) (KFlatDGResolution.canonical A C)
            (KFlatDGResolution.canonical A E)) (canonicalComparisonComposeIso A P' Q' R')))
      ((whiskeringLeft _ _ _).obj (canonicalComparisonEquivalence A P Q).functor) ≪≫
    Functor.isoWhiskerRight (canonicalComparisonComposeIso A P Q R)
      ((whiskeringRight _ _ _).obj (canonicalComparisonEquivalence A P' R').inverse)

end SerrePositivity.DifferentialGraded.ResolutionBimodule
