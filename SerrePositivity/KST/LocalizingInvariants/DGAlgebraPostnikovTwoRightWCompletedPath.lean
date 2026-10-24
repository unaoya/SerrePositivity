module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightWZeroFollowing

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorRightWCompletedPath

/-!
概要：元の後続輸送と完成模型への復元の合成から、W 終点の native 零経路を回収する。
方針：元の実模型の両脚と全 path を計算し、動く底の終点へ照合する。
規約：完成模型射を別の候補へ置き換えない。使われ方：native 模型経路の a₁ 入力。
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

set_option quotPrecheck false
local notation "α" => SquareZeroExtension.relativeLeft
  (d.rightClassifyingLayer R) (d.rightImageClass R)
local notation "β" => SquareZeroExtension.relativeRight
  (d.rightClassifyingLayer R) (d.rightImageClass R)
local notation "K" => d.rightClassifyingLayer R
local notation "a" => d.rightImageClass R
local notation "a'" => d.fixedRightCompletedClass R
local notation "V" => postnikov R (B.obj j).obj 1
local notation "N" => postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1
local notation "C" => postnikovPerturbedClass R (B.obj j).obj 1 (by omega)
local notation "b'" => postnikovCommonClassRightDenominatorBase R f
  d.baseInverse d.layerInverse d.target_le

def rightWCompletedModel :=
  PostnikovSuccessorClassInverseData.rightWCompletedModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWCompletedModel_left : d.rightWCompletedModel R ≫
    HomotopyPullbackModel.left R C (SquareZero.zeroSection V N) =
    α ≫ d.fixedRightCompletedNativeSource R :=
  PostnikovSuccessorClassInverseData.rightWCompletedModel_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWCompletedModel_right : d.rightWCompletedModel R ≫
    HomotopyPullbackModel.right R C (SquareZero.zeroSection V N) = β ≫ b' :=
  PostnikovSuccessorClassInverseData.rightWCompletedModel_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWCompletedModel_path : d.rightWCompletedModel R ≫
    HomotopyPullbackModel.path R C (SquareZero.zeroSection V N) =
    (SquareZeroExtension.transport K (d.fixedRightFollowingWitness R) ≫
      SquareZeroExtension.relativePath K a') ≫ Path.map R (d.rightDenominatorClassRestore R) :=
  PostnikovSuccessorClassInverseData.rightWCompletedModel_path
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightDenominatorClassRestore_projection : d.rightDenominatorClassRestore R ≫
    SquareZero.projection V N = SquareZero.projection (d.classBase R) K ≫ b' :=
  PostnikovSuccessorClassInverseData.rightDenominatorClassRestore_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightCompletedClass_projection : a' ≫ SquareZero.projection (d.classBase R) K =
    d.classProjection R :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedClass_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWCompletedModel_path_base : (d.rightWCompletedModel R ≫
    HomotopyPullbackModel.path R C (SquareZero.zeroSection V N)) ≫
      Path.map R (SquareZero.projection V N) = (β ≫ b') ≫ Path.diagonal R V :=
  PostnikovSuccessorClassInverseData.rightWCompletedModel_path_base
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightWCompletedNativePath : Path.Witness R
    ((α ≫ d.fixedRightCompletedNativeSource R) ≫ C)
    ((d.rightWBasePath R ≫ Path.target R V) ≫ SquareZero.zeroSection V N) :=
  PostnikovSuccessorClassInverseData.rightWCompletedNativePath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWCompletedNativePath_projection : (d.rightWCompletedNativePath R).hom ≫
    Path.map R (SquareZero.projection V N) =
      (d.rightWBasePath R ≫ Path.target R V) ≫ Path.diagonal R V :=
  PostnikovSuccessorClassInverseData.rightWCompletedNativePath_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
