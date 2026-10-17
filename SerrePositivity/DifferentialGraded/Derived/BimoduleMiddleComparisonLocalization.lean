module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparisonFamily

/-! # 中間圏の導来合成比較を前因子の全導来圏へ降ろす -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)

lemma middleDerivedSourceFamily_inverts :
    (BimoduleCategory.quasiIso A B C).IsInvertedBy
      (middleDerivedSourceFamily A B C D E F hE Q) := by
  intro P P' f hf
  have hr : BimoduleCategory.quasiIso A B D
      (BimoduleCategory.middleLeftRestrictionMap A B C D F f) :=
    fun b d => hf b (F.obj d)
  have : IsIso ((bimoduleToDerived A B D).map
      (BimoduleCategory.middleLeftRestrictionMap A B C D F f)) :=
    bimoduleToDerived_inverts A B D _ hr
  exact ((derivedBimoduleComposeFunctor A B D E hE).obj
    ((bimoduleToDerived A D E).obj
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))).map_isIso
      ((bimoduleToDerived A B D).map (BimoduleCategory.middleLeftRestrictionMap A B C D F f))

/-- 中間圏を制限してから導来合成する関手を、指定準同型の局所化へ延長する。 -/
def middleDerivedSourceLift : DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E :=
  bimoduleDerivedLift A B C (middleDerivedSourceFamily A B C D E F hE Q)
    (middleDerivedSourceFamily_inverts A B C D E F hE Q)

lemma middleDerivedSourceLift_fac :
    bimoduleToDerived A B C ⋙ middleDerivedSourceLift A B C D E F hE Q =
      middleDerivedSourceFamily A B C D E F hE Q :=
  bimoduleDerivedLift_fac A B C _ _

instance middleDerivedSourceLift_lifting :
    Localization.Lifting (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (middleDerivedSourceFamily A B C D E F hE Q) (middleDerivedSourceLift A B C D E F hE Q) :=
  ⟨eqToIso (middleDerivedSourceLift_fac A B C D E F hE Q)⟩

instance middleDerivedTargetFamily_lifting :
    Localization.Lifting (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (middleDerivedTargetFamily A B C E hE Q)
      ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj)) :=
  ⟨Iso.refl _⟩

/-- 前因子の全導来圏上の自然変換。後因子と制限後の解像度は指定されたものを使う。 -/
def derivedMiddleRestrictionComparisonLocalized (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) :
    middleDerivedSourceLift A B C D E F hE Q ⟶
      (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj) :=
  Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (middleDerivedSourceFamily A B C D E F hE Q) (middleDerivedTargetFamily A B C E hE Q)
    (middleDerivedSourceLift A B C D E F hE Q)
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
    (derivedMiddleRestrictionComparisonFamily A B C D E F hE Q R q hq)

/-- 局所化前の対象で、前項の実際の比較射を計算する式。 -/
lemma derivedMiddleRestrictionComparisonLocalized_app (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) (P : BimoduleCategory A B C) :
    (derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q R q hq).app
        ((bimoduleToDerived A B C).obj P) =
      (Localization.Lifting.iso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
        (middleDerivedSourceFamily A B C D E F hE Q)
        (middleDerivedSourceLift A B C D E F hE Q)).hom.app P ≫
      derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq ≫
      (Localization.Lifting.iso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
        (middleDerivedTargetFamily A B C E hE Q)
        ((derivedBimoduleComposeFunctor A B C E hE).obj
          ((bimoduleToDerived A C E).obj Q.obj))).inv.app P := by
  have h := Localization.liftNatTrans_app (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C) (middleDerivedSourceFamily A B C D E F hE Q)
    (middleDerivedTargetFamily A B C E hE Q) (middleDerivedSourceLift A B C D E F hE Q)
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
    (derivedMiddleRestrictionComparisonFamily A B C D E F hE Q R q hq) P
  rw [derivedMiddleRestrictionComparisonFamily_app] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
