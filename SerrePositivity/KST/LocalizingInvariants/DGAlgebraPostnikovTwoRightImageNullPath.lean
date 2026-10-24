module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightImageSourcePath
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroSourceModelHomotopy

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorRightImageNullPath

/-!
概要：元の右像の相対模型が持つ零経路を、Bⱼ の native class 標的へ戻す。
方針：元の relativePath を係数復元で移し、両脚と底の定数経路を保持する。
規約：零経路の存在を追加仮定にしない。使われ方：source 自然性と W の実模型比較。
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

lemma rightImageClass_projection : d.rightImageClass R ≫ SquareZero.projection _ _ =
    d.classProjection R :=
  PostnikovSuccessorClassInverseData.rightImageClass_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightImageRelativeRight :
    SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.rightImageClass R) =
    SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      d.classProjection R :=
  PostnikovSuccessorClassInverseData.rightImageRelativeRight
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightImageNativeNullPath : SquareZero.RelativeWitness
    (SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le)
    (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)
    ((SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      d.rightImageNativeSource R) ≫ postnikovPerturbedClass R (B.obj j).obj 1 (by omega))
    ((SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le) ≫
        SquareZero.zeroSection (postnikov R (B.obj j).obj 1)
          (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)) :=
  PostnikovSuccessorClassInverseData.rightImageNativeNullPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightImageModelSourcePath : Path.Witness R
    (SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      d.rightImageNativeSource R)
    (SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      ((postnikovCommonRightGammaSourceWitness R f d.baseInverse d.layerInverse d.target_le).hom ≫
        Path.source R (postnikovPerturbedExtension R (B.obj j).obj 1 (by omega)))) :=
  PostnikovSuccessorClassInverseData.rightImageModelSourcePath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightImageModelSourcePath_relative :
    ((d.rightImageModelSourcePath R).postcomp
      (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))).hom ≫
        Path.map R (SquareZero.projection _ _) =
    (SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
      postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le) ≫
        Path.diagonal R (postnikov R (B.obj j).obj 1) :=
  PostnikovSuccessorClassInverseData.rightImageModelSourcePath_relative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightImageSourceModelHomotopy :=
  PostnikovSuccessorClassInverseData.rightImageSourceModelHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightImageOriginalModel_as_lift :
    SquareZeroExtension.sourceModelInitialMap
      (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1)
      (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))
      (SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
        postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le)
      (d.rightImageNativeNullPath R) = d.rightImageRelativeToOriginalModel R :=
  PostnikovSuccessorClassInverseData.rightImageOriginalModel_as_lift
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightImageToGammaModel :=
  PostnikovSuccessorClassInverseData.rightImageToGammaModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightImageOriginalSourceModelHomotopy : Path.Witness R
    (d.rightImageRelativeToOriginalModel R) (d.rightImageToGammaModel R) :=
  PostnikovSuccessorClassInverseData.rightImageOriginalSourceModelHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
