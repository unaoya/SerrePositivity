module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSourceIdentification

/-! # 全導来中間比較を既存の導来制限・導来合成のsourceに移す -/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

/-- 後因子の右K-flat部分圏上でのsource表示の自然同型。 -/
def middleSourceKFlatIdentification :
    middleDerivedSourceKFlatFunctor A B C D E F hE ≅
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        middleRestrictionDerivedSource A B C D E F hE :=
  NatIso.ofComponents (middleDerivedSourceLiftIdentification A B C D E F hE)
    (fun g => middleDerivedSourceLiftIdentification_naturality A B C D E F hE g)

lemma middleSourceKFlatTarget_fac :
    rightKFlatToDerived A C E ⋙
        (rightKFlatDerivedInclusion A C E ⋙ middleRestrictionDerivedSource A B C D E F hE) =
      rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        middleRestrictionDerivedSource A B C D E F hE := by
  rw [← Functor.assoc, rightKFlatDerivedInclusion_fac]
  rfl

instance middleSourceKFlatTarget_lifting :
    Localization.Lifting (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
      (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
        middleRestrictionDerivedSource A B C D E F hE)
      (rightKFlatDerivedInclusion A C E ⋙ middleRestrictionDerivedSource A B C D E F hE) :=
  ⟨eqToIso (middleSourceKFlatTarget_fac A B C D E F hE)⟩

/-- 後因子の指定準同型の局所化上でのsource表示の自然同型。 -/
def middleRightKFlatSourceIdentification :
    middleRightKFlatLocalizedSource A B C D E F hE ≅
      rightKFlatDerivedInclusion A C E ⋙ middleRestrictionDerivedSource A B C D E F hE :=
  Localization.liftNatIso (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
    (middleDerivedSourceKFlatFunctor A B C D E F hE)
    (rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙
      middleRestrictionDerivedSource A B C D E F hE)
    (middleRightKFlatLocalizedSource A B C D E F hE)
    (rightKFlatDerivedInclusion A C E ⋙ middleRestrictionDerivedSource A B C D E F hE)
    (middleSourceKFlatIdentification A B C D E F hE)

/-- 両変数の全導来圏上で、比較のsourceを既存の導来制限と導来合成へ同定する。 -/
def middleFullDerivedSourceIdentification :
    middleFullDerivedSource A B C D E F hE ≅
      middleRestrictionDerivedSource A B C D E F hE :=
  Functor.isoWhiskerLeft (derivedRightKFlatReplacement A C E hE)
      (middleRightKFlatSourceIdentification A B C D E F hE) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightKFlatReplacementCounitIso A C E hE)
      (middleRestrictionDerivedSource A B C D E F hE) ≪≫ Functor.leftUnitor _

/-- 既存の導来制限と導来合成の間の、両変数の全導来射に自然な中間圏比較。 -/
def derivedMiddleRestrictionNatTrans :
    middleRestrictionDerivedSource A B C D E F hE ⟶
      derivedBimoduleComposeFunctor A B C E hE :=
  (middleFullDerivedSourceIdentification A B C D E F hE).inv ≫
    middleFullDerivedComparison A B C D E F hE

lemma derivedMiddleRestrictionNatTrans_transport :
    (middleFullDerivedSourceIdentification A B C D E F hE).hom ≫
        derivedMiddleRestrictionNatTrans A B C D E F hE =
      middleFullDerivedComparison A B C D E F hE := by
  unfold derivedMiddleRestrictionNatTrans
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- source表示同型による移送を各導来対象で計算する。 -/
lemma derivedMiddleRestrictionNatTrans_app
    (Q : DerivedBimoduleCategory A C E) (P : DerivedBimoduleCategory A B C) :
    ((derivedMiddleRestrictionNatTrans A B C D E F hE).app Q).app P =
      ((middleFullDerivedSourceIdentification A B C D E F hE).inv.app Q).app P ≫
        ((middleFullDerivedComparison A B C D E F hE).app Q).app P := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
