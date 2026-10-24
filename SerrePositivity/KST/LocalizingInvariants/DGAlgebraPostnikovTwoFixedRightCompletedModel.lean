module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightCompletedSquare
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassHomotopy

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightCompletedModel

/-!
概要：元の fixed 模型射の接合合成と、直接分母遷移の class 模型射を実経路で比較する。
方針：実二重 class 経路を係数模型射で前合成し、接合合成の厳密な式へ戻す。
規約：元の fixed 模型合成を終点に持つ。使われ方：元の代数 roof の右三角形照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def fixedRightDirectModelMap :=
  PostnikovSuccessorClassInverseData.fixedRightDirectModelMap
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedRightCompletedModelHomotopy : Path.Witness R
    (d.fixedRightDirectModelMap R) (d.sourceToRightCompletedModel R) :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedModelHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightCompletedModelHomotopy_left : (d.fixedRightCompletedModelHomotopy R).hom ≫
    Path.map R (SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R) _) =
      SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) ≫
        Path.diagonal R (d.classSource R) :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedModelHomotopy_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightCompletedModelHomotopy_right : (d.fixedRightCompletedModelHomotopy R).hom ≫
    Path.map R (SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) _) =
      SquareZeroExtension.relativeRight (d.denominatorLayer R) (d.sourceClass R) ≫
        Path.diagonal R (d.classBase R) :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedModelHomotopy_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
