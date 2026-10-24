module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightCompletedModel
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassTargetModel
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientRestore

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightImageRestore

/-!
概要：fixed の fⱼ 係数像の零底表示を、元の Bⱼ の class 標的へ戻す。
方針：元の底射の等式と係数同型を使い、元の fⱼ の係数三角形を保つ。
規約：元の Bⱼ の実係数を回収。使われ方：標的比較と元の fⱼ の模型射への接続。
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

def rightImageCoefficientIso :
    bimoduleRestrict
      (postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le)
      (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≅
    d.rightClassifyingLayer R :=
  PostnikovSuccessorClassInverseData.rightImageCoefficientIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightTargetCoefficient_factor : d.rightTargetCoefficient R =
    postnikovCellClassOverCoefficient R (A.obj j).obj (B.obj j).obj (d.classBase R)
      1 (by omega) (d.targetBase R) (f.app j).hom ≫ (d.rightImageCoefficientIso R).hom :=
  PostnikovSuccessorClassInverseData.rightTargetCoefficient_factor
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightImageClassRestore :=
  PostnikovSuccessorClassInverseData.rightImageClassRestore
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightTargetCoefficient_restore :
    SquareZero.coefficientMap (d.classBase R) (d.rightTargetCoefficient R) ≫
      d.rightImageClassRestore R =
    SquareZero.baseChangeMap (d.targetBase R)
      (postnikovShiftedLayerBimodule R (A.obj j).obj 1 (by omega) 1) ≫
      postnikovDerivationTargetMap R (f.app j).hom 1 (by omega) :=
  PostnikovSuccessorClassInverseData.rightTargetCoefficient_restore
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
