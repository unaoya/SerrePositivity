module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightOriginalRoof

/-!
概要：直接分母遷移の元の係数表示を classifying 表示へ同型化し、元の標的へ戻す。
方針：元の二段分母の表示同型を双加群上で合成し、同じ平方零同型を回収する。
規約：直接分母経路の元の係数射を保持。使われ方：輸送後の模型の標的復元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def rightDenominatorCoefficientIso : bimoduleRestrict
    (postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse d.target_le)
    (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≅
      d.rightClassifyingLayer R :=
  bimoduleRestrictBaseEqIso (postnikovCellFactorizationImage_base R
    (B.obj d.layerInverse.zero.stage).obj (B.obj j).obj (d.classBase R) 1
    (d.lowerBaseInverse R).roof.denominator
    (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le)
    (B.obj d.inverseStage).obj
    (B.transition (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le)).hom
    (B.transition d.target_le).hom
    (postnikovCommonRightDenDirect_factorization R f d.baseInverse d.layerInverse d.target_le))
    (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≪≫
  postnikovClassBaseZeroCoefficientIso R (B.obj j).obj (d.classBase R) 1 (by omega) 1
    (postnikovCommonRightDenCompositeBase R f d.baseInverse d.layerInverse d.target_le) ≪≫
  bimoduleRestrictBaseEqIso
    (postnikovCommonRightDenComposite_zero_base R f d.baseInverse d.layerInverse d.target_le)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)

lemma rightDenominatorCoefficientIso_map :
    (SquareZero.coefficientIso (d.classBase R) (d.rightDenominatorCoefficientIso R)).hom =
      postnikovCommonRightDenDirectToZero R f d.baseInverse d.layerInverse d.target_le := by
  simp only [rightDenominatorCoefficientIso, Iso.trans_hom, SquareZero.coefficientIso_hom,
    postnikovCommonRightDenDirectToZero, postnikovCommonRightDenDirectImageIso,
    postnikovCellFactorizationImageIso, postnikovCommonRightDenCompositeZeroIso,
    postnikovClassZeroRebaseIso, postnikovClassBaseZeroIso, SquareZero.restrictionEqualityIso,
    Iso.trans_hom, SquareZero.coefficientIso_hom, ← SquareZero.coefficientMap_comp]
  rfl

def rightDenominatorClassRestore := SquareZero.coefficientRestore
  (postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse d.target_le)
  (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)
  (d.rightDenominatorCoefficientIso R)

lemma rightDenominatorClassRestore_triangle :
    postnikovCommonRightDenDirectToZero R f d.baseInverse d.layerInverse d.target_le ≫
      d.rightDenominatorClassRestore R = SquareZero.baseChangeMap
        (postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse d.target_le)
        (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) := by
  rw [← d.rightDenominatorCoefficientIso_map R]
  exact SquareZero.coefficientRestore_triangle _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
