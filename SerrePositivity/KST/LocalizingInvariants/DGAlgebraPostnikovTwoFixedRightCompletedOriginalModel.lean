module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightCompletedClass

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightCompletedOriginalModel

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def fixedRightCompletedNativeSource :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedNativeSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedRightCompletedToOriginalModel :
    SquareZeroExtension.model (d.rightClassifyingLayer R) (d.fixedRightCompletedClass R) ⟶
      postnikovClassModel R (B.obj j).obj 1 (by omega) :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedToOriginalModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightCompletedToOriginalModel_left : d.fixedRightCompletedToOriginalModel R ≫
    HomotopyPullbackModel.left R _ _ = HomotopyPullbackModel.left R _ _ ≫
      d.fixedRightCompletedNativeSource R :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedToOriginalModel_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightCompletedToOriginalModel_right : d.fixedRightCompletedToOriginalModel R ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ ≫
      postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse d.target_le :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedToOriginalModel_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightCompletedToOriginalModel_path : d.fixedRightCompletedToOriginalModel R ≫
    HomotopyPullbackModel.path R _ _ = HomotopyPullbackModel.path R _ _ ≫
      Path.map R (d.rightDenominatorClassRestore R) :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedToOriginalModel_path
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedRightCompletedRelativeToOriginalModel : SquareZeroExtension.relativeModel
    (d.rightClassifyingLayer R) (d.fixedRightCompletedClass R) ⟶
      postnikovClassModel R (B.obj j).obj 1 (by omega) :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedRelativeToOriginalModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedRightCompletedOriginalModelHomotopy : Path.Witness R
    (d.fixedRightDirectModelMap R ≫ d.fixedRightCompletedRelativeToOriginalModel R)
    (d.sourceToRightCompletedModel R ≫ d.fixedRightCompletedRelativeToOriginalModel R) :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedOriginalModelHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
