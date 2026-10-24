module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightWInitialPath

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorRightWZeroFollowing

/-!
概要：fⱼ 自然性・W・元の零経路を同じ零底で比較し、後続輸送の全経路を回収する。
方針：元の全 class 像と affine 反転・合成の保存則を使う。
規約：経路の端点一致だけでは比較しない。使われ方：native 模型の k₁ 入力。
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
local notation "V" => postnikov R (B.obj j).obj 1
local notation "V₀" => postnikov R (B.obj j).obj 0
local notation "N" => postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1
local notation "N₀" => DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1
local notation "C" => postnikovPerturbedClass R (B.obj j).obj 1 (by omega)
local notation "q" => postnikovTransition R (B.obj j).obj 1 0 (by omega)
local notation "z" => postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1
local notation "b" => postnikovCommonRightClassifyingBase R f
  d.baseInverse d.layerInverse d.target_le
local notation "q₀" => β ≫ b
local notation "vₙ" => SquareZeroExtension.sourceModelClassWitness N C
  (β ≫ postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le)
  (d.rightImageModelSourcePath R) (d.rightImageModelSourcePath_relative R)
local notation "v₀" => postnikovCommonClassFixedRightNaturality R f
  d.baseInverse d.layerInverse d.target_le
local notation "w₀" => postnikovCommonClassFixedRightBottom R f
  d.baseInverse d.layerInverse d.target_le d.inverse

def rightNatZeroSourcePath :=
  PostnikovSuccessorClassInverseData.rightNatZeroSourcePath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightOriginalZeroNullPath :=
  PostnikovSuccessorClassInverseData.rightOriginalZeroNullPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightNatZeroSourcePath_hom : (d.rightNatZeroSourcePath R).hom = α ≫ (v₀).hom :=
  PostnikovSuccessorClassInverseData.rightNatZeroSourcePath_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWZeroSourcePath_hom : (d.rightWZeroSourcePath R).hom = α ≫ (w₀).hom :=
  PostnikovSuccessorClassInverseData.rightWZeroSourcePath_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightFollowingZeroRawPath :=
  PostnikovSuccessorClassInverseData.rightFollowingZeroRawPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightFollowingZeroRawPath_hom : (d.rightFollowingZeroRawPath R).hom =
    ((d.rightNatZeroSourcePath R).comp (d.rightWZeroSourcePath R)).hom :=
  PostnikovSuccessorClassInverseData.rightFollowingZeroRawPath_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightFollowingZeroPath :=
  PostnikovSuccessorClassInverseData.rightFollowingZeroPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightFollowingZeroPath_hom : (d.rightFollowingZeroPath R).hom =
    ((d.rightNatZeroSourcePath R).comp (d.rightWZeroSourcePath R)).hom :=
  PostnikovSuccessorClassInverseData.rightFollowingZeroPath_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWInitialZeroPath_nested : (d.rightWInitialZeroPath R).hom =
    ((d.rightNatZeroSourcePath R).reverse.comp (d.rightOriginalZeroNullPath R)).hom :=
  PostnikovSuccessorClassInverseData.rightWInitialZeroPath_nested
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWZeroNull_composite :
    ((d.rightFollowingZeroPath R).reverse.comp (d.rightOriginalZeroNullPath R)).hom =
    ((d.rightWZeroSourcePath R).reverse.comp (d.rightWInitialZeroPath R)).hom :=
  PostnikovSuccessorClassInverseData.rightWZeroNull_composite
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
