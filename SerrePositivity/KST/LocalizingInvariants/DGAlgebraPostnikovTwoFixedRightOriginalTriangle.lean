module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightImageModel
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoTargetModelProjections

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightOriginalTriangle

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def rightImageRelativeToOriginalModel :=
  PostnikovSuccessorClassInverseData.rightImageRelativeToOriginalModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma targetToRightCoefficientModel_original : d.targetToRightCoefficientModel R ≫
    d.rightImageRelativeToOriginalModel R = d.targetRelativeComparison R ≫
      d.targetToOriginalModel R ≫ postnikovClassModelMap R 1 (by omega) (f.app j).hom :=
  PostnikovSuccessorClassInverseData.targetToRightCoefficientModel_original
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToRightCoefficientModel_original : d.sourceToRightCoefficientModel R ≫
    d.rightImageRelativeToOriginalModel R = d.sourceToTargetFixedRelative R ≫
      d.targetRelativeComparison R ≫ d.targetToOriginalModel R ≫
        postnikovClassModelMap R 1 (by omega) (f.app j).hom :=
  PostnikovSuccessorClassInverseData.sourceToRightCoefficientModel_original
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
