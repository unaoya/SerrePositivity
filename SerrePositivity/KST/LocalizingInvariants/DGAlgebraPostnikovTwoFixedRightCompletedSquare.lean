module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightFollowing
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenDirectRestored

/-!
概要：元の fixed 模型の接合 class 経路を、元の直接分母遷移と実二重経路で比較する。
方針：底と零 class の全射影の一意性で復元経路を回収し、全二重経路を移送する。
規約：元の fixed 模型 class と Γ 射影を保持。使われ方：実右模型三角形の照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma fixedRightCompletedWitness_restored_hom :
    (d.fixedRightCompletedWitness R).hom =
      (postnikovCommonClassFixedRightRestoredPath R f d.baseInverse d.layerInverse
        d.target_le d.inverse).hom := by
  apply SquareZero.baseChangePath_hom_ext
    (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
  · exact (d.fixedRightCompletedWitness R).projection_eq.trans
      (postnikovCommonClassFixedRightRestoredPath R f d.baseInverse d.layerInverse
        d.target_le d.inverse).projection_eq.symm
  · exact (d.fixedRightCompletedWitness_zero_map R).trans
      (postnikovCommonClassFixedRightRestoredPath_map R f d.baseInverse d.layerInverse
        d.target_le d.inverse).symm

def fixedRightDirectWitness := SquareZero.RelativeWitness.transferEndpoints
  (postnikovCommonClassFixedRightRestoredPath R f d.baseInverse d.layerInverse
    d.target_le d.inverse) (d.fixedRightCompletedWitness R)
  (d.fixedRightCompletedWitness_restored_hom R).symm
  (postnikovCommonRightDenDirectContourPath R f d.baseInverse d.layerInverse d.target_le)

lemma fixedRightDirectWitness_hom : (d.fixedRightDirectWitness R).hom =
    (postnikovCommonRightDenDirectContourPath R f d.baseInverse d.layerInverse
      d.target_le).hom := by
  let h := SquareZero.RelativeWitness.transferEndpoints_hom
    (postnikovCommonClassFixedRightRestoredPath R f d.baseInverse d.layerInverse
      d.target_le d.inverse) (d.fixedRightCompletedWitness R)
    (d.fixedRightCompletedWitness_restored_hom R).symm
    (postnikovCommonRightDenDirectContourPath R f d.baseInverse d.layerInverse d.target_le)
  exact h

def fixedRightCompletedSquare : SquareZero.RelativeWitnessSquare
    (d.fixedRightDirectWitness R) (d.fixedRightCompletedWitness R) :=
  (postnikovCommonRightDenDirectRestoredSquare R f d.baseInverse d.layerInverse
    d.target_le d.inverse).reindex _ _ (d.fixedRightDirectWitness_hom R).symm
      (d.fixedRightCompletedWitness_restored_hom R).symm

def fixedRightCompletedTransportHomotopy :=
  SquareZeroExtension.transportHomotopy (d.rightClassifyingLayer R)
    (d.fixedRightCompletedSquare R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
