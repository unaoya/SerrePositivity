module
public import SerrePositivity.DifferentialGraded.Perfect.RingExtensions
public import Mathlib.CategoryTheory.Shift.CommShift

/-! # 一対象Aの通常複体比較と導来比較の整合的shift

既存の実際の評価との自然同型を、完全忠実な評価に沿って持ち上げる。
shiftの零・和coherenceと比較自然変換の整合性を同時に得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 通常複体から一対象dg加群への比較のshiftは、実際の評価を通じて一意に整合する。 -/
instance complexToRingModuleCommShift : (complexToRingModule A).CommShift ℤ :=
  Functor.CommShift.ofComp (complexToRingModuleEvaluationIso A) ℤ

/-- 評価との恒等比較は零・加法coherenceを持つshiftに整合する。 -/
instance complexToRingModuleEvaluationIsoCommShift :
    NatTrans.CommShift (complexToRingModuleEvaluationIso A).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (complexToRingModuleEvaluationIso A) ℤ

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 主導来評価と既存Qとの比較も整数shiftに整合する。 -/
instance complexToRingModuleDerivedEvaluationIsoCommShift :
    NatTrans.CommShift (complexToRingModuleDerivedEvaluationIso A).hom ℤ := by
  have : NatTrans.CommShift (Functor.isoWhiskerLeft (complexToRingModule A)
      (ringDerivedEquivalence_fac A)).hom ℤ := by
    change NatTrans.CommShift (Functor.whiskerLeft _ (ringDerivedEquivalence_fac A).hom) ℤ
    infer_instance
  have : NatTrans.CommShift (Functor.isoWhiskerRight
      (complexToRingModuleEvaluationIso A) (DerivedCategory.Q (C := ModuleCat.{u} A))).hom ℤ := by
    change NatTrans.CommShift (Functor.whiskerRight (complexToRingModuleEvaluationIso A).hom _) ℤ
    infer_instance
  dsimp only [complexToRingModuleDerivedEvaluationIso, Iso.trans_hom, Iso.symm_hom]
  apply NatTrans.CommShift.comp

/-- 既存一対象導来同値の順逆のshiftはunit/counitとも整合する。 -/
instance ringDerivedEquivalenceShiftCompatible : (ringDerivedEquivalence A).CommShift ℤ :=
  Equivalence.CommShift.mk'' _ _ (ringDerivedEquivalenceCounitCommShift A)

/-- 既存導来圏から一対象同値の逆で戻す比較を、全複体に自然な同型として公開する。 -/
def ringComplexDerivedUnitNatIso :
    DerivedCategory.Q (C := ModuleCat.{u} A) ⋙ (ringDerivedEquivalence A).inverse ≅
      complexToRingModule A ⋙ moduleToDerived A PUnit.{1} :=
  Functor.isoWhiskerRight (complexToRingModuleDerivedEvaluationIso A).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (complexToRingModule A ⋙ moduleToDerived A PUnit.{1})
      (ringDerivedEquivalence A).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- 逆比較自然同型も、既存の導来同値のshiftと整合する。 -/
instance ringComplexDerivedUnitNatIsoCommShift :
    NatTrans.CommShift (ringComplexDerivedUnitNatIso A).hom ℤ := by
  have : NatTrans.CommShift (Functor.isoWhiskerRight
      (complexToRingModuleDerivedEvaluationIso A).symm
      (ringDerivedEquivalence A).inverse).hom ℤ := by
    change NatTrans.CommShift (Functor.whiskerRight
      (complexToRingModuleDerivedEvaluationIso A).inv (ringDerivedEquivalence A).inverse) ℤ
    infer_instance
  have : NatTrans.CommShift (Functor.isoWhiskerLeft
      (complexToRingModule A ⋙ moduleToDerived A PUnit.{1})
      (ringDerivedEquivalence A).unitIso.symm).hom ℤ := by
    change NatTrans.CommShift (Functor.whiskerLeft _ (ringDerivedEquivalence A).unitIso.inv) ℤ
    infer_instance
  dsimp only [ringComplexDerivedUnitNatIso, Iso.trans_hom, Iso.symm_hom]
  apply NatTrans.CommShift.comp

end SerrePositivity.DifferentialGraded
