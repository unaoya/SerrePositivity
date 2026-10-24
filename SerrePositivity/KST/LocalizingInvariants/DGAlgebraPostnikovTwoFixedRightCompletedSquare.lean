module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightFollowing
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenDirectRestored

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightCompletedSquare

/-!
概要：元の fixed 模型の接合 class 経路を、元の直接分母遷移と実二重経路で比較する。
方針：底と零 class の全射影の一意性で復元経路を回収し、全二重経路を移送する。
規約：元の fixed 模型 class と Γ 射影を保持。使われ方：実右模型三角形の照合。
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

lemma fixedRightCompletedWitness_restored_hom :
    (d.fixedRightCompletedWitness R).hom =
      (postnikovCommonClassFixedRightRestoredPath R f d.baseInverse d.layerInverse
        d.target_le d.inverse).hom :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedWitness_restored_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedRightDirectWitness :=
  PostnikovSuccessorClassInverseData.fixedRightDirectWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightDirectWitness_hom : (d.fixedRightDirectWitness R).hom =
    (postnikovCommonRightDenDirectContourPath R f d.baseInverse d.layerInverse
      d.target_le).hom :=
  PostnikovSuccessorClassInverseData.fixedRightDirectWitness_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedRightCompletedSquare : SquareZero.RelativeWitnessSquare
    (d.fixedRightDirectWitness R) (d.fixedRightCompletedWitness R) :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedRightCompletedTransportHomotopy :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
