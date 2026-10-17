module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleKFlatFamily

/-! # 両因子の全導来bimodule圏上の中間dg圏比較自然変換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

/-- 後因子も指定準同型の局所化へ降ろしたsource関手族。 -/
def middleRightKFlatLocalizedSource : DerivedRightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  Localization.Construction.lift (middleDerivedSourceKFlatFunctor A B C D E F hE)
    (middleDerivedSourceKFlatFunctor_inverts A B C D E F hE)

lemma middleRightKFlatLocalizedSource_fac :
    rightKFlatToDerived A C E ⋙ middleRightKFlatLocalizedSource A B C D E F hE =
      middleDerivedSourceKFlatFunctor A B C D E F hE := Localization.Construction.fac _ _

instance middleRightKFlatLocalizedSource_lifting :
    Localization.Lifting (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
      (middleDerivedSourceKFlatFunctor A B C D E F hE)
      (middleRightKFlatLocalizedSource A B C D E F hE) :=
  ⟨eqToIso (middleRightKFlatLocalizedSource_fac A B C D E F hE)⟩

lemma middleRightKFlatLocalizedTarget_fac :
    rightKFlatToDerived A C E ⋙
        (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE) =
      middleDerivedTargetKFlatFunctor A B C E hE := by
  rw [← Functor.assoc, rightKFlatDerivedInclusion_fac]
  rfl

instance middleRightKFlatLocalizedTarget_lifting :
    Localization.Lifting (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
      (middleDerivedTargetKFlatFunctor A B C E hE)
      (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE) :=
  ⟨eqToIso (middleRightKFlatLocalizedTarget_fac A B C E hE)⟩

def middleRightKFlatLocalizedComparison :
    middleRightKFlatLocalizedSource A B C D E F hE ⟶
      rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE :=
  Localization.liftNatTrans (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
    (middleDerivedSourceKFlatFunctor A B C D E F hE) (middleDerivedTargetKFlatFunctor A B C E hE)
    (middleRightKFlatLocalizedSource A B C D E F hE)
    (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE)
    (middleDerivedKFlatComparison A B C D E F hE)

lemma middleRightKFlatLocalizedComparison_app (Q : RightKFlatBimoduleCategory A C E) :
    (middleRightKFlatLocalizedComparison A B C D E F hE).app ((rightKFlatToDerived A C E).obj Q) =
      (Localization.Lifting.iso (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
        (middleDerivedSourceKFlatFunctor A B C D E F hE)
        (middleRightKFlatLocalizedSource A B C D E F hE)).hom.app Q ≫
      derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q ≫
      (Localization.Lifting.iso (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
        (middleDerivedTargetKFlatFunctor A B C E hE)
        (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE)).inv.app Q :=
  Localization.liftNatTrans_app _ _ _ _ _ _ _ _

/-- 後因子の既存K-flat置換を通した、両変数の全導来圏上のsource。 -/
def middleFullDerivedSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  derivedRightKFlatReplacement A C E hE ⋙ middleRightKFlatLocalizedSource A B C D E F hE

/-- 後因子の既存置換同値の余単位と導来合成との比較。 -/
def middleFullDerivedTargetIso :
    derivedRightKFlatReplacement A C E hE ⋙
        (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE) ≅
      derivedBimoduleComposeFunctor A B C E hE :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightKFlatReplacementCounitIso A C E hE)
      (derivedBimoduleComposeFunctor A B C E hE) ≪≫ Functor.leftUnitor _

/-- 中間圏の制限と導来合成の比較。両変数とも実際の全導来bimodule圏上で自然。 -/
def middleFullDerivedComparison :
    middleFullDerivedSource A B C D E F hE ⟶ derivedBimoduleComposeFunctor A B C E hE :=
  whiskerLeft (derivedRightKFlatReplacement A C E hE)
    (middleRightKFlatLocalizedComparison A B C D E F hE) ≫
      (middleFullDerivedTargetIso A B C E hE).hom

lemma middleFullDerivedComparison_app (Q : DerivedBimoduleCategory A C E) :
    (middleFullDerivedComparison A B C D E F hE).app Q =
      (middleRightKFlatLocalizedComparison A B C D E F hE).app
        ((derivedRightKFlatReplacement A C E hE).obj Q) ≫
          (middleFullDerivedTargetIso A B C E hE).hom.app Q := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
