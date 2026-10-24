module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassSourceModel

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassTargetModel

/-!
概要：共通底の標準 class 模型から、元の A の低い段の class 模型への実射を構成する。
方針：同じ分子と class の底変更式を cospan 射へ渡し、元の摂動比較へ接続する。
規約：標的比較の準同型性は仮定しない。使われ方：元の二切断への分子の回収。
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

def targetBase : d.classBase R ⟶ postnikov R (A.obj j).obj 1 :=
  PostnikovSuccessorClassInverseData.targetBase
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def targetCellMap : d.classSource R ⟶ cellResolution R (postnikov R (A.obj j).obj 1) :=
  PostnikovSuccessorClassInverseData.targetCellMap
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

abbrev targetCellModel : Mon (Complex R) :=
  PostnikovSuccessorClassInverseData.targetCellModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (j := j)

abbrev originalTargetModel : Mon (Complex R) :=
  PostnikovSuccessorClassInverseData.originalTargetModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (j := j)

def targetToCellModel : d.targetModel R ⟶ targetCellModel (A := A) (j := j) R :=
  PostnikovSuccessorClassInverseData.targetToCellModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def targetToOriginalModel : d.targetModel R ⟶ originalTargetModel (A := A) (j := j) R :=
  PostnikovSuccessorClassInverseData.targetToOriginalModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma targetToOriginalModel_right : d.targetToOriginalModel R ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ ≫
      (d.lowerBaseInverse R).roof.numerator :=
  PostnikovSuccessorClassInverseData.targetToOriginalModel_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
