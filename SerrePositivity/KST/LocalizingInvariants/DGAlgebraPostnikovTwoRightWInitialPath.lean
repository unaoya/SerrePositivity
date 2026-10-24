module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightWSource
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeNullComposition

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorRightWInitialPath

/-!
概要：fⱼ 自然性の終点の零経路と、W の全 class 経路を同じ零底に揃える。
方針：元の native 零経路を affine 輸送し、動く底の始点と零切断の式で照合する。
規約：零経路と全 W 経路を実構成する。使われ方：native 模型経路の a₀・v・p 入力。
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
local notation "E" => postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)
local notation "C" => postnikovPerturbedClass R (B.obj j).obj 1 (by omega)
local notation "q" => postnikovTransition R (B.obj j).obj 1 0 (by omega)
local notation "z" => postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1
local notation "r" => d.rightWBasePath R
local notation "q₀" => β ≫ postnikovCommonRightClassifyingBase R f
  d.baseInverse d.layerInverse d.target_le
local notation "l₀" => α ≫ ((postnikovCommonRightGammaSourceWitness R f
  d.baseInverse d.layerInverse d.target_le).hom ≫ Path.source R E)
local notation "l₁" => α ≫ d.fixedRightCompletedNativeSource R

def rightGammaNativeNullPath :=
  PostnikovSuccessorClassInverseData.rightGammaNativeNullPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightWInitialNativePath : SquareZero.RelativeWitness (r ≫ Path.source R V) N
    (l₀ ≫ C) ((r ≫ Path.source R V) ≫ SquareZero.zeroSection V N) :=
  PostnikovSuccessorClassInverseData.rightWInitialNativePath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWZeroBase_source : (r ≫ Path.source R V) ≫ q = q₀ :=
  PostnikovSuccessorClassInverseData.rightWZeroBase_source
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightWZeroSourcePath : SquareZero.RelativeWitness q₀ N₀
    ((l₀ ≫ C) ≫ z) ((l₁ ≫ C) ≫ z) :=
  PostnikovSuccessorClassInverseData.rightWZeroSourcePath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightWInitialZeroPath : SquareZero.RelativeWitness q₀ N₀
    ((l₀ ≫ C) ≫ z) (q₀ ≫ SquareZero.zeroSection V₀ N₀) :=
  PostnikovSuccessorClassInverseData.rightWInitialZeroPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWSource_nativeClass : ((d.rightWSourcePath R).hom ≫ Path.map R C) ≫
    Path.map R ((postnikovNativeZeroIso R (B.obj j).obj 1 (by omega) 1).hom ≫
      SquareZero.baseChangeMap q N₀) = (d.rightWZeroSourcePath R).hom :=
  PostnikovSuccessorClassInverseData.rightWSource_nativeClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightWInitial_nativeClass : (d.rightWInitialNativePath R).hom ≫
    Path.map R ((postnikovNativeZeroIso R (B.obj j).obj 1 (by omega) 1).hom ≫
      SquareZero.baseChangeMap q N₀) = (d.rightWInitialZeroPath R).hom :=
  PostnikovSuccessorClassInverseData.rightWInitial_nativeClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
