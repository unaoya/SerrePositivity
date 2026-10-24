module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightCompletedClass

/-!
概要：接合後の元の模型を Bⱼ の摂動模型へ戻し、元の実模型経路をそこへ移す。
方針：直接分母の終点 class 復元を同じ実 cospan 射にし、元の経路を後合成する。
規約：元の fixed 合成と直接分母模型射を保持。使われ方：実右逆三角形の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

def fixedRightCompletedNativeSource := d.fixedRightCompletedCellMap R ≫
  postnikovCellLift R (B.obj j).obj n hn

def fixedRightCompletedToOriginalModel :
    SquareZeroExtension.model (d.rightClassifyingLayer R) (d.fixedRightCompletedClass R) ⟶
      postnikovClassModel R (B.obj j).obj n hn :=
  HomotopyPullbackModel.map R (d.fixedRightCompletedClass R) _
    (postnikovPerturbedClass R (B.obj j).obj n hn) _
    (d.fixedRightCompletedNativeSource R) (d.rightDenominatorClassRestore R)
    (PostnikovCommonCore.postnikovCommonClassRightDenominatorBase R hn f d.baseInverse d.layerInverse d.target_le)
    (by simpa only [fixedRightCompletedNativeSource, postnikovCellClass, Category.assoc] using
      (d.fixedRightCompletedClass_restore R).symm)
    (SquareZero.coefficientRestore_zeroSection _ _ _).symm

lemma fixedRightCompletedToOriginalModel_left : d.fixedRightCompletedToOriginalModel R ≫
    HomotopyPullbackModel.left R _ _ = HomotopyPullbackModel.left R _ _ ≫
      d.fixedRightCompletedNativeSource R := HomotopyPullbackModel.map_left R _ _ _ _ _ _ _ _ _

lemma fixedRightCompletedToOriginalModel_right : d.fixedRightCompletedToOriginalModel R ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ ≫
      PostnikovCommonCore.postnikovCommonClassRightDenominatorBase R hn f d.baseInverse d.layerInverse d.target_le :=
  HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _

lemma fixedRightCompletedToOriginalModel_path : d.fixedRightCompletedToOriginalModel R ≫
    HomotopyPullbackModel.path R _ _ = HomotopyPullbackModel.path R _ _ ≫
      Path.map R (d.rightDenominatorClassRestore R) :=
  HomotopyPullbackModel.map_path R _ _ _ _ _ _ _ _ _

def fixedRightCompletedRelativeToOriginalModel : SquareZeroExtension.relativeModel
    (d.rightClassifyingLayer R) (d.fixedRightCompletedClass R) ⟶
      postnikovClassModel R (B.obj j).obj n hn :=
  SquareZeroExtension.relativeComparison (d.rightClassifyingLayer R)
    (d.fixedRightCompletedClass R) ≫ d.fixedRightCompletedToOriginalModel R

def fixedRightCompletedOriginalModelHomotopy : Path.Witness R
    (d.fixedRightDirectModelMap R ≫ d.fixedRightCompletedRelativeToOriginalModel R)
    (d.sourceToRightCompletedModel R ≫ d.fixedRightCompletedRelativeToOriginalModel R) :=
  (d.fixedRightCompletedModelHomotopy R).postcomp (d.fixedRightCompletedRelativeToOriginalModel R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
