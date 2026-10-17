module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSourceFull
public import Mathlib.Data.ZMod.Basic

/-! # 両変数の全導来中間比較と既存の制限・合成APIへのsource同定の検査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

-- C・Dの局所Hom K-flat性や制限後のK-flat性を仮定しない。
example : middleFullDerivedSource A B C D E F hE ≅
    middleRestrictionDerivedSource A B C D E F hE :=
  middleFullDerivedSourceIdentification A B C D E F hE

example (Q : DerivedBimoduleCategory A C E) (P : DerivedBimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B D E hE).obj
      ((derivedBimoduleRestriction A D E C E F (DGFunctor.id E)).obj Q)).obj
      ((derivedBimoduleRestriction A B D B C (DGFunctor.id B) F).obj P) ⟶
    ((derivedBimoduleComposeFunctor A B C E hE).obj Q).obj P :=
  ((derivedMiddleRestrictionNatTrans A B C D E F hE).app Q).app P

example {Q Q' : DerivedBimoduleCategory A C E} (g : Q ⟶ Q') :
    (middleRestrictionDerivedSource A B C D E F hE).map g ≫
        (derivedMiddleRestrictionNatTrans A B C D E F hE).app Q' =
      (derivedMiddleRestrictionNatTrans A B C D E F hE).app Q ≫
        (derivedBimoduleComposeFunctor A B C E hE).map g :=
  (derivedMiddleRestrictionNatTrans A B C D E F hE).naturality g

example (Q : DerivedBimoduleCategory A C E) {P P' : DerivedBimoduleCategory A B C}
    (f : P ⟶ P') :
    ((middleRestrictionDerivedSource A B C D E F hE).obj Q).map f ≫
        ((derivedMiddleRestrictionNatTrans A B C D E F hE).app Q).app P' =
      ((derivedMiddleRestrictionNatTrans A B C D E F hE).app Q).app P ≫
        ((derivedBimoduleComposeFunctor A B C E hE).obj Q).map f :=
  ((derivedMiddleRestrictionNatTrans A B C D E F hE).app Q).naturality f

example (X : Type v) (Y : Type w) (Z : Type z) (T : Type t)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [DGCategory (ZMod 2) Z] [DGCategory (ZMod 2) T]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z] [Small.{0} T]
    (G : DGFunctor (ZMod 2) Z Y) (hT : localHomKFlat (ZMod 2) T) :
    middleRestrictionDerivedSource (ZMod 2) X Y Z T G hT ⟶
      derivedBimoduleComposeFunctor (ZMod 2) X Y T hT :=
  derivedMiddleRestrictionNatTrans (ZMod 2) X Y Z T G hT

namespace SerrePositivity.DifferentialGraded
#print axioms BimoduleTensorModule.middleLeftPresentationObjIso
#print axioms BimoduleTensorModule.middleLeftPresentationObjIso_hom_eval
#print axioms BimoduleTensorModule.middleLeftPresentationIso
#print axioms BimoduleTensorModule.middleRightPresentationObjIso
#print axioms BimoduleTensorModule.middleRightPresentationObjIso_hom_eval
#print axioms BimoduleTensorModule.middleRightPresentationIso
#print axioms middleLeftRestrictionIso
#print axioms middleRightRestrictionIso
#print axioms middleLeftRestrictionDerivedIso
#print axioms middleRightRestrictionDerivedIso
#print axioms BimoduleTensor.middleRestrictionDerivedSource
#print axioms BimoduleTensor.middleClosedSourceFunctor
#print axioms BimoduleTensor.middleClosedSourceIdentification
#print axioms BimoduleTensor.middleDerivedSourceFamilyIdentification
#print axioms BimoduleTensor.middleRestrictionSourceTarget_lifting
#print axioms BimoduleTensor.middleDerivedSourceLiftIdentification
#print axioms BimoduleTensor.middleRestrictionSourceTargetMap_lift
#print axioms BimoduleTensor.middleDerivedSourceLiftIdentification_naturality
#print axioms BimoduleTensor.middleSourceKFlatIdentification
#print axioms BimoduleTensor.middleSourceKFlatTarget_fac
#print axioms BimoduleTensor.middleSourceKFlatTarget_lifting
#print axioms BimoduleTensor.middleRightKFlatSourceIdentification
#print axioms BimoduleTensor.middleFullDerivedSourceIdentification
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_transport
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_app
end SerrePositivity.DifferentialGraded
