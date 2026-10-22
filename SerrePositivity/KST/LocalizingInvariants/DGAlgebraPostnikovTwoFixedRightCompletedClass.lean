module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDenRestore
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessEndpoints

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

def fixedRightCompletedClass := (d.fixedRightCompletedWitness R).targetMap

lemma fixedRightDirectWitness_targetMap : (d.fixedRightDirectWitness R).targetMap =
    d.fixedRightCompletedClass R := by
  let h := SquareZero.RelativeWitness.targetMap_eq (d.fixedRightDirectWitness R)
  let k := SquareZero.RelativeWitness.targetMap_eq (d.fixedRightCompletedWitness R)
  exact h.trans k.symm

lemma fixedRightCompletedClass_direct : d.fixedRightCompletedClass R =
    postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse ≫
      (cellAugmentation R (cellResolution R (d.classBase R)) ≫
        postnikovCellClassOver R (B.obj j).obj (d.classBase R) 1 (by omega)
          (postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse
            d.target_le)) ≫
      postnikovCommonRightDenDirectToZero R f d.baseInverse d.layerInverse d.target_le := by
  let v := postnikovCellImageRelative R (B.obj d.layerInverse.zero.stage).obj (B.obj j).obj
    (d.classBase R) 1 (by omega) (d.lowerBaseInverse R).roof.denominator
    (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le)
  let h := (d.fixedRightDirectWitness_hom R).trans
    ((postnikovCommonRightDenDirectContourPath_hom R f d.baseInverse d.layerInverse
      d.target_le).trans
      (postnikovCommonRightDenDirectPath_hom R f d.baseInverse d.layerInverse d.target_le))
  let k := SquareZero.RelativeWitness.targetMap_whisker (d.fixedRightDirectWitness R) v
    (postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse)
    (postnikovCommonRightDenDirectToZero R f d.baseInverse d.layerInverse d.target_le) h
  exact (d.fixedRightDirectWitness_targetMap R).symm.trans k

def fixedRightCompletedCellMap :=
  postnikovCommonRightImageToSecond R f d.baseInverse d.layerInverse ≫
    cellAugmentation R (cellResolution R (d.classBase R)) ≫
      cellResolutionMap R
        (postnikovCommonClassRightDenominatorBase R f d.baseInverse d.layerInverse d.target_le)

lemma fixedRightCompletedClass_restore :
    d.fixedRightCompletedClass R ≫ d.rightDenominatorClassRestore R =
      d.fixedRightCompletedCellMap R ≫ postnikovCellClass R (B.obj j).obj 1 (by omega) := by
  rw [d.fixedRightCompletedClass_direct R]
  simp only [Category.assoc]
  rw [d.rightDenominatorClassRestore_triangle R, postnikovCellClassOver_map]
  simp only [fixedRightCompletedCellMap, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
