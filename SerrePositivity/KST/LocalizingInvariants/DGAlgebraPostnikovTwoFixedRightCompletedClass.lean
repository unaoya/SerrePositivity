module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDenRestore
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessEndpoints

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightCompletedClass

/-!
概要：自然性と W の接合後の元の class を、直接分母遷移の終点として回収する。
方針：指定された全直接経路の式を終点で評価し、元の係数復元の三角形を使う。
規約：元の completed 証人の終点を保持。使われ方：同じ Bⱼ 模型への実比較。
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

def fixedRightCompletedClass :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightDirectWitness_targetMap : (d.fixedRightDirectWitness R).targetMap =
    d.fixedRightCompletedClass R :=
  PostnikovSuccessorClassInverseData.fixedRightDirectWitness_targetMap
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightCompletedClass_direct : d.fixedRightCompletedClass R =
    postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse ≫
      (cellAugmentation R (cellResolution R (d.classBase R)) ≫
        postnikovCellClassOver R (B.obj j).obj (d.classBase R) 1 (by omega)
          (postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse
            d.target_le)) ≫
      postnikovCommonRightDenDirectToZero R f d.baseInverse d.layerInverse d.target_le :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedClass_direct
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedRightCompletedCellMap :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedCellMap
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightCompletedClass_restore :
    d.fixedRightCompletedClass R ≫ d.rightDenominatorClassRestore R =
      d.fixedRightCompletedCellMap R ≫ postnikovCellClass R (B.obj j).obj 1 (by omega) :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedClass_restore
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
