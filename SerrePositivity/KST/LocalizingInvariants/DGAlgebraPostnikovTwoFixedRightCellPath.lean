module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightImageValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellComparePathPairs

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightCellPath

/-!
概要：元の fixed 模型射の fⱼ 後合成と直接遷移を、三重 cell 源上の実経路で結ぶ。
方針：右像からの二経路と直接側の二経路を、指定した同じ完成射で接続する。
規約：局所化後の射の一致から経路を選ばない。使われ方：τ₂ の実 roof の右三角形。
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

def fixedTargetModelMap :=
  PostnikovSuccessorClassInverseData.fixedTargetModelMap
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedRightImageToCompletedModelHomotopy : Path.Witness R
    (d.sourceToRightCoefficientModel R ≫ d.rightImageToGammaModel R)
    (d.sourceToRightCompletedModel R ≫ d.fixedRightCompletedRelativeToOriginalModel R) :=
  PostnikovSuccessorClassInverseData.fixedRightImageToCompletedModelHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedRightClassModelPath : Path.Witness R
    (iteratedCellAugmentation R (d.sourceRelativeModel R) 3 ≫
      (d.fixedTargetModelMap R ≫ postnikovClassModelMap R 1 (by omega) (f.app j).hom))
    (iteratedCellAugmentation R (d.sourceRelativeModel R) 3 ≫ d.directOriginalModelMap R) :=
  PostnikovSuccessorClassInverseData.fixedRightClassModelPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
