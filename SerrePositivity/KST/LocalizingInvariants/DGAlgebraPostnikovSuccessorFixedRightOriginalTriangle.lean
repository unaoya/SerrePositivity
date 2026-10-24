module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightImageModel
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorTargetModelProjections

/-!
概要：fixed の右係数模型合成を、元の標的比較と fⱼ の実模型射の合成へ同定する。
方針：元の二脚と全経路を、係数復元の厳密な三角形で同時に比較する。
規約：元の fixed 射と元の fⱼ を保持。使われ方：実 roof の右逆三角形への接続。
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

def rightImageRelativeToOriginalModel :=
  SquareZeroExtension.relativeComparison (d.rightClassifyingLayer R) (d.rightImageClass R) ≫
    d.rightImageToOriginalModel R

lemma targetToRightCoefficientModel_original : d.targetToRightCoefficientModel R ≫
    d.rightImageRelativeToOriginalModel R = d.targetRelativeComparison R ≫
      d.targetToOriginalModel R ≫ postnikovClassModelMap R n hn (f.app j).hom := by
  let M := d.numeratorLayer R
  let N := d.rightClassifyingLayer R
  let a := d.targetClass R
  let b := d.rightImageClass R
  let m := d.rightTargetCoefficient R
  let hL := SquareZeroExtension.coefficientModelMap_left m a b rfl
  let hR := SquareZeroExtension.coefficientModelMap_right m a b rfl
  let hP := SquareZeroExtension.coefficientModelMap_path m a b rfl
  let iL := SquareZeroExtension.relativeComparison_left N b
  let iR := SquareZeroExtension.relativeComparison_right N b
  let iP := SquareZeroExtension.relativeComparison_path N b
  let tL := SquareZeroExtension.relativeComparison_left M a
  let tR := SquareZeroExtension.relativeComparison_right M a
  let tP := SquareZeroExtension.relativeComparison_path M a
  apply HomotopyPullbackModel.hom_ext R (postnikovPerturbedClass R (B.obj j).obj n hn)
    (SquareZero.zeroSection (postnikov R (B.obj j).obj n)
      (postnikovShiftedLayerBimodule R (B.obj j).obj n hn 1))
  · simp only [rightImageRelativeToOriginalModel, targetToRightCoefficientModel,
      targetRelativeComparison, Category.assoc, d.rightImageToOriginalModel_left R,
      postnikovClassModelMap_left, reassoc_of% (d.targetToOriginalModel_left R)]
    rw [reassoc_of% iL, reassoc_of% hL, reassoc_of% tL]
    simp only [rightImageNativeSource, Category.assoc]
    rfl
  · simp only [rightImageRelativeToOriginalModel, targetToRightCoefficientModel,
      targetRelativeComparison, Category.assoc, d.rightImageToOriginalModel_right R,
      postnikovClassModelMap_right, reassoc_of% (d.targetToOriginalModel_base R)]
    rw [reassoc_of% iR, reassoc_of% hR, reassoc_of% tR]
    rfl
  · simp only [rightImageRelativeToOriginalModel, targetToRightCoefficientModel,
      targetRelativeComparison, Category.assoc, d.rightImageToOriginalModel_path R,
      postnikovClassModelMap_path, reassoc_of% (d.targetToOriginalModel_path R)]
    rw [reassoc_of% iP, reassoc_of% hP, reassoc_of% tP]
    let h := Category.assoc (SquareZeroExtension.relativePath M a)
      (Path.map R (SquareZero.coefficientMap (d.classBase R) m))
      (Path.map R (d.rightImageClassRestore R))
    let k := congrArg (fun t => SquareZeroExtension.relativePath M a ≫ t)
      (Path.map_comp R (SquareZero.coefficientMap (d.classBase R) m)
        (d.rightImageClassRestore R)).symm
    let g := congrArg (fun t => SquareZeroExtension.relativePath M a ≫ Path.map R t)
      (d.rightTargetCoefficient_restore R)
    let z := congrArg (fun t => SquareZeroExtension.relativePath M a ≫ t)
      (Path.map_comp R (SquareZero.baseChangeMap (d.targetBase R)
        (postnikovShiftedLayerBimodule R (A.obj j).obj n hn 1))
        (postnikovDerivationTargetMap R (f.app j).hom n hn))
    exact ((h.trans k).trans g).trans z

lemma sourceToRightCoefficientModel_original : d.sourceToRightCoefficientModel R ≫
    d.rightImageRelativeToOriginalModel R = d.sourceToTargetFixedRelative R ≫
      d.targetRelativeComparison R ≫ d.targetToOriginalModel R ≫
        postnikovClassModelMap R n hn (f.app j).hom := by
  rw [sourceToRightCoefficientModel, Category.assoc, d.targetToRightCoefficientModel_original R]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
