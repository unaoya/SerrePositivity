module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightWCompletedZero

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorRightWModelHomotopy

/-!
概要：元の相対模型上で W の動く source を native 模型へ実適用する。
方針：全 class 経路と両端の零経路を実入力し、両脚と全 path で元の模型射へ戻す。
規約：右像からの一定底の自然性経路と合わせて使う。使われ方：fixed 右三角形の値の比較。
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
local notation "β" => SquareZeroExtension.relativeRight
  (d.rightClassifyingLayer R) (d.rightImageClass R)
local notation "V" => postnikov R (B.obj j).obj 1
local notation "V₀" => postnikov R (B.obj j).obj 0
local notation "N" => postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1
local notation "N₀" => DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1
local notation "C" => postnikovPerturbedClass R (B.obj j).obj 1 (by omega)
local notation "q" => postnikovTransition R (B.obj j).obj 1 0 (by omega)
local notation "e" => postnikovNativeZeroCoefficientIso R (B.obj j).obj 1 (by omega) 1
local notation "r" => d.rightWBasePath R
local notation "q₀" => β ≫ postnikovCommonRightClassifyingBase R f
  d.baseInverse d.layerInverse d.target_le

def rightWNativeModelHomotopy :=
  PostnikovSuccessorClassInverseData.rightWNativeModelHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWInitialModel_eq : HomotopyPullbackModel.lift R C (SquareZero.zeroSection V N)
    _ (r ≫ Path.source R V) (d.rightWInitialNativePath R).toWitness =
      d.rightImageToGammaModel R :=
  PostnikovSuccessorClassInverseData.rightWInitialModel_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWCompletedModel_eq : HomotopyPullbackModel.lift R C (SquareZero.zeroSection V N)
    _ (r ≫ Path.target R V) (d.rightWCompletedNativePath R) = d.rightWCompletedModel R :=
  PostnikovSuccessorClassInverseData.rightWCompletedModel_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightWModelHomotopy : Path.Witness R (d.rightImageToGammaModel R)
    (d.rightWCompletedModel R) :=
  PostnikovSuccessorClassInverseData.rightWModelHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
