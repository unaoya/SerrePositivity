module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition

/-! # 右K-flatモデル上の自然同型を既存の全導来関手間へ移す -/
@[expose] public section
noncomputable section
universe u v w z z'
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (E : Type w) [DGCategory A E] [Small.{u} E] (hE : localHomKFlat A E)
  {T : Type z} [Category.{z'} T]

/-- 指定右K-flatモデル上の自然同型を、右K-flat部分圏の局所化上へ移す。 -/
def rightKFlatLocalizedIsoOfPrecomp (G H : DerivedBimoduleCategory A C E ⥤ T)
    (e : rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ G ≅
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ H) :
      rightKFlatDerivedInclusion A C E ⋙ G ≅ rightKFlatDerivedInclusion A C E ⋙ H := by
  letI sourceLifting : Localization.Lifting (rightKFlatToDerived A C E)
      (rightKFlatQuasiIso A C E)
      (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ G)
      (rightKFlatDerivedInclusion A C E ⋙ G) :=
    ⟨Functor.isoWhiskerRight (eqToIso (rightKFlatDerivedInclusion_fac A C E)) G⟩
  letI targetLifting : Localization.Lifting (rightKFlatToDerived A C E)
      (rightKFlatQuasiIso A C E)
      (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ H)
      (rightKFlatDerivedInclusion A C E ⋙ H) :=
    ⟨Functor.isoWhiskerRight (eqToIso (rightKFlatDerivedInclusion_fac A C E)) H⟩
  exact Localization.liftNatIso (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
    _ _ (rightKFlatDerivedInclusion A C E ⋙ G) (rightKFlatDerivedInclusion A C E ⋙ H) e

/-- 指定右K-flatモデル上の自然同型を、指定局所化と置換余単位で全導来圏へ移す。 -/
def rightKFlatDerivedIsoOfPrecomp (G H : DerivedBimoduleCategory A C E ⥤ T)
    (e : rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ G ≅
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ H) : G ≅ H := by
  let e' := rightKFlatLocalizedIsoOfPrecomp A C E G H e
  exact (Functor.isoWhiskerRight (rightKFlatReplacementCounitIso A C E hE) G ≪≫
      Functor.leftUnitor G).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedRightKFlatReplacement A C E hE) e' ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightKFlatReplacementCounitIso A C E hE) H ≪≫
    Functor.leftUnitor H

variable (B : Type z) [DGCategory A B] [Small.{u} B]

/-- 閉零右K-flatモデルへの前合成では、既存の全導来合成は固定因子関手族に自然同型。 -/
def rightKFlatComposePresentationIso :
    rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        derivedBimoduleComposeFunctor A B C E hE ≅
      derivedComposeWithFunctor A B C E :=
  Functor.isoWhiskerRight (eqToIso (rightKFlatDerivedInclusion_fac A C E)).symm
      (derivedBimoduleComposeFunctor A B C E hE) ≪≫
    Functor.isoWhiskerLeft (rightKFlatToDerived A C E)
      (derivedBimoduleComposeKFlatFamilyIso A B C E hE) ≪≫
    eqToIso (rightFactorLocalizedComposeFunctor_fac A B C E)

end SerrePositivity.DifferentialGraded.BimoduleTensor
