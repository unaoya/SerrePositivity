module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectInitialComparison
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroClassModelPathImage

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectFinalProjections

/-!
概要：source 模型経路の終点の二脚と全 class 経路を、元の fixed class 証人へ揃える。
方針：source 経路の class 像と、保存済みの直接 class 復元式を合成する。
規約：元の実 class 経路を保持。使われ方：終点模型射の三成分比較。
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

def directSourceClassWitness :=
  PostnikovSuccessorClassInverseData.directSourceClassWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma directSourceFinalModelMap_left : d.directSourceFinalModelMap R ≫
    HomotopyPullbackModel.left R _ _ =
    SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) ≫
      d.fixedRightCompletedNativeSource R :=
  PostnikovSuccessorClassInverseData.directSourceFinalModelMap_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma directSourceFinalModelMap_right : d.directSourceFinalModelMap R ≫
    HomotopyPullbackModel.right R _ _ = d.directRelativeBase R :=
  PostnikovSuccessorClassInverseData.directSourceFinalModelMap_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma directSourceFinalModelMap_path : d.directSourceFinalModelMap R ≫
    HomotopyPullbackModel.path R _ _ =
      ((d.directSourceClassWitness R).reverse.comp (d.directInitialNativeWitness R)).hom :=
  PostnikovSuccessorClassInverseData.directSourceFinalModelMap_path
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightDirectModelMap_left : d.fixedRightDirectModelMap R ≫
    SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R) (d.fixedRightCompletedClass R) =
    SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) :=
  PostnikovSuccessorClassInverseData.fixedRightDirectModelMap_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightDirectModelMap_right : d.fixedRightDirectModelMap R ≫
    SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.fixedRightCompletedClass R) =
    SquareZeroExtension.relativeRight (d.denominatorLayer R) (d.sourceClass R) :=
  PostnikovSuccessorClassInverseData.fixedRightDirectModelMap_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightCompletedClass_native : d.fixedRightCompletedClass R ≫
    d.rightDenominatorClassRestore R =
    d.fixedRightCompletedNativeSource R ≫ postnikovPerturbedClass R (B.obj j).obj 1 (by omega) :=
  PostnikovSuccessorClassInverseData.fixedRightCompletedClass_native
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma directSourceClassWitness_restore : (d.directSourceClassWitness R).hom =
    SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) ≫
      (d.fixedRightDirectWitness R).hom ≫ Path.map R (d.rightDenominatorClassRestore R) :=
  PostnikovSuccessorClassInverseData.directSourceClassWitness_restore
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
