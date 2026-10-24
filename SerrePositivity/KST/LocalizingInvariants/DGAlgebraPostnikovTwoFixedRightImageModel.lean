module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightImageRestore
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassModelMap

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightImageModel

/-!
概要：fixed の fⱼ 係数像の模型から、元の Bⱼ の摂動 class 模型への実射を構成する。
方針：係数復元と元の cell 比較・摂動自然性を、同じ実 cospan 射にする。
規約：元の fⱼ と元の二脚を保持。使われ方：fixed roof の標的比較の回収。
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

lemma targetClass_baseChange : d.targetClass R ≫ SquareZero.baseChangeMap (d.targetBase R)
    (postnikovShiftedLayerBimodule R (A.obj j).obj 1 (by omega) 1) =
    d.targetCellMap R ≫ postnikovCellClass R (A.obj j).obj 1 (by omega) :=
  PostnikovSuccessorClassInverseData.targetClass_baseChange
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightImageNativeSource :=
  PostnikovSuccessorClassInverseData.rightImageNativeSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightImageClass_restore : d.rightImageClass R ≫ d.rightImageClassRestore R =
    d.rightImageNativeSource R ≫ postnikovPerturbedClass R (B.obj j).obj 1 (by omega) :=
  PostnikovSuccessorClassInverseData.rightImageClass_restore
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightImageToOriginalModel :
    SquareZeroExtension.model (d.rightClassifyingLayer R) (d.rightImageClass R) ⟶
      postnikovClassModel R (B.obj j).obj 1 (by omega) :=
  PostnikovSuccessorClassInverseData.rightImageToOriginalModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightImageToOriginalModel_left : d.rightImageToOriginalModel R ≫
    HomotopyPullbackModel.left R _ _ =
      HomotopyPullbackModel.left R _ _ ≫
        d.rightImageNativeSource R :=
  PostnikovSuccessorClassInverseData.rightImageToOriginalModel_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightImageToOriginalModel_right : d.rightImageToOriginalModel R ≫
    HomotopyPullbackModel.right R _ _ =
      HomotopyPullbackModel.right R _ _ ≫
        postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le :=
  PostnikovSuccessorClassInverseData.rightImageToOriginalModel_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightImageToOriginalModel_path : d.rightImageToOriginalModel R ≫
    HomotopyPullbackModel.path R _ _ =
      HomotopyPullbackModel.path R _ _ ≫
        Path.map R (d.rightImageClassRestore R) :=
  PostnikovSuccessorClassInverseData.rightImageToOriginalModel_path
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
