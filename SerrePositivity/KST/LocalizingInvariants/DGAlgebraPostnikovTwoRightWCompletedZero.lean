module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightWCompletedPath

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorRightWCompletedZero

/-!
概要：完成模型の零 class 経路を、W の反転と始点零経路の合成に同定する。
方針：係数復元・輸送・反転合成の全射を同じ零底へ写す。
規約：指定した完成模型の全 path を保持。使われ方：movingSourceNativeModelHomotopy の k₁。
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
local notation "V" => postnikov R (B.obj j).obj 1
local notation "N" => postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1
local notation "N₀" => DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1
local notation "q" => postnikovTransition R (B.obj j).obj 1 0 (by omega)
local notation "z" => postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1
local notation "b" => postnikovCommonRightClassifyingBase R f
  d.baseInverse d.layerInverse d.target_le
local notation "q₀" => β ≫ b
local notation "u" => d.fixedRightFollowingWitness R
local notation "k" => SquareZero.baseChangeMap b N₀
local notation "hk" => SquareZero.baseChangeMap_projection b N₀

def rightOriginalCoefficientZeroNullPath :=
  PostnikovSuccessorClassInverseData.rightOriginalCoefficientZeroNullPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightOriginalCoefficientZeroNullPath_hom :
    (d.rightOriginalCoefficientZeroNullPath R).hom = (d.rightOriginalZeroNullPath R).hom :=
  PostnikovSuccessorClassInverseData.rightOriginalCoefficientZeroNullPath_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWCompletedNativePath_zeroClass : (d.rightWCompletedNativePath R).hom ≫
    Path.map R z =
    ((d.rightWZeroSourcePath R).reverse.comp (d.rightWInitialZeroPath R)).hom :=
  PostnikovSuccessorClassInverseData.rightWCompletedNativePath_zeroClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWCompletedNativePath_nativeClass : (d.rightWCompletedNativePath R).hom ≫
    Path.map R ((postnikovNativeZeroIso R (B.obj j).obj 1 (by omega) 1).hom ≫
      SquareZero.baseChangeMap q N₀) =
    ((d.rightWZeroSourcePath R).reverse.comp (d.rightWInitialZeroPath R)).hom :=
  PostnikovSuccessorClassInverseData.rightWCompletedNativePath_nativeClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
