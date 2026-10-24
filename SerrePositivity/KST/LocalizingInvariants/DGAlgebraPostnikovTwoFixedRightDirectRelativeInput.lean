module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectSourceWitness
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeImageWitness
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSourceChange

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectRelativeInput

/-!
概要：元の source 相対模型から、source 模型ホモトピーの実経路と相対 class 入力を構成する。
方針：元の相対模型経路を係数復元で写し、同じ source 自然性の始点へ表示を揃える。
規約：元の相対経路と右脚を保持。使われ方：直接 B 遷移の実模型比較。
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

def directRelativeBase :=
  PostnikovSuccessorClassInverseData.directRelativeBase
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def directRelativeSourcePath :=
  PostnikovSuccessorClassInverseData.directRelativeSourcePath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def directInitialNativeWitness : SquareZero.RelativeWitness (d.directRelativeBase R)
    (directNativeLayer (B := B) (j := j) R)
    ((SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) ≫
      d.directNativeSource R) ≫ postnikovPerturbedClass R (B.obj j).obj 1 (by omega))
    (d.directRelativeBase R ≫ SquareZero.zeroSection (postnikov R (B.obj j).obj 1)
      (directNativeLayer (B := B) (j := j) R)) :=
  PostnikovSuccessorClassInverseData.directInitialNativeWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma directInitialNativeWitness_hom : (d.directInitialNativeWitness R).hom =
    SquareZeroExtension.relativePath (d.denominatorLayer R) (d.sourceClass R) ≫
      Path.map R (d.directNativeClassMap R) :=
  PostnikovSuccessorClassInverseData.directInitialNativeWitness_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma directRelativeSourcePath_class_relative :
    ((d.directRelativeSourcePath R).postcomp
      (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))).hom ≫
      Path.map R (SquareZero.projection (postnikov R (B.obj j).obj 1)
        (directNativeLayer (B := B) (j := j) R)) =
    d.directRelativeBase R ≫ Path.diagonal R (postnikov R (B.obj j).obj 1) :=
  PostnikovSuccessorClassInverseData.directRelativeSourcePath_class_relative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
