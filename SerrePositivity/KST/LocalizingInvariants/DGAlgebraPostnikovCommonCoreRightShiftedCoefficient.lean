module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreShiftedInverse
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleShiftFromRestriction

/-!
概要：元の細分 roof 底上の右係数比較を、class の shift 係数へ移す。
方針：元の分子・分母の shift 制限から、同じ右標的の shift へ実射を作る。
規約：元の右 cochain 三角形を保持。使われ方：実平方零 class 標的の可換式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) (s : ℤ)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonRightShiftedNumeratorMap :
    roofShiftedNumeratorLayer R hn f (roofRefine R hn f c d.zero.source_le) s ⟶
      DGBimoduleShift.obj (postnikovCommonRightLayer R hn f c d) s :=
  DGBimoduleShift.fromRestriction _ _ _ s (postnikovCommonRightNumeratorMap R hn f c d)

lemma postnikovCommonRightShiftedNumeratorMap_hom :
    (postnikovCommonRightShiftedNumeratorMap R hn f c d s).hom =
      (postnikovLayerMap R (f.app i).hom n)⟦s⟧' :=
  (DGBimoduleShift.fromRestriction_hom _ _ _ s
    (postnikovCommonRightNumeratorMap R hn f c d)).trans
      (congrArg (fun t => t⟦s⟧') (postnikovCommonRightNumeratorMap_hom R hn f c d))

def postnikovCommonRightShiftedDenominatorMap :
    roofShiftedDenominatorLayer R hn f (roofRefine R hn f c d.zero.source_le) s ⟶
      DGBimoduleShift.obj (postnikovCommonRightLayer R hn f c d) s :=
  DGBimoduleShift.fromRestriction _ _ _ s (postnikovCommonRightDenominatorMap R hn f c d)

lemma postnikovCommonRightShiftedDenominatorMap_hom :
    (postnikovCommonRightShiftedDenominatorMap R hn f c d s).hom =
      (postnikovLayerMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom n)⟦s⟧' :=
  (DGBimoduleShift.fromRestriction_hom _ _ _ s
    (postnikovCommonRightDenominatorMap R hn f c d)).trans
      (congrArg (fun t => t⟦s⟧') (postnikovCommonRightDenominatorMap_hom R hn f c d))

lemma postnikovCommonRightShifted_coefficient : postnikovCommonShiftedCoefficientMap R hn f c d s ≫
    postnikovCommonRightShiftedNumeratorMap R hn f c d s =
      postnikovCommonRightShiftedDenominatorMap R hn f c d s := by
  apply Bimod.Hom.ext
  exact (Bimod.comp_hom' _ _).trans
    ((congrArg (fun t => (postnikovCommonShiftedCoefficientMap R hn f c d s).hom ≫ t)
      (postnikovCommonRightShiftedNumeratorMap_hom R hn f c d s)).trans
        ((postnikovCommonShiftedCoefficientMap_right R hn f c d s).trans
          (postnikovCommonRightShiftedDenominatorMap_hom R hn f c d s).symm))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
