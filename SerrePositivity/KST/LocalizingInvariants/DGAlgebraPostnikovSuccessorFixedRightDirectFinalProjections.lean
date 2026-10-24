module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectInitialComparison
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroClassModelPathImage

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

def directSourceClassWitness := SquareZeroExtension.sourceModelClassWitness
  (directNativeLayer (n := n) (hn := hn) (B := B) (j := j) R)
  (postnikovPerturbedClass R (B.obj j).obj n hn) (d.directRelativeBase R)
  (d.directRelativeSourcePath R) (d.directRelativeSourcePath_class_relative R)

lemma directSourceFinalModelMap_left : d.directSourceFinalModelMap R ≫
    HomotopyPullbackModel.left R _ _ =
    SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) ≫
      d.fixedRightCompletedNativeSource R := HomotopyPullbackModel.lift_left R _ _ _ _ _

lemma directSourceFinalModelMap_right : d.directSourceFinalModelMap R ≫
    HomotopyPullbackModel.right R _ _ = d.directRelativeBase R :=
  HomotopyPullbackModel.lift_right R _ _ _ _ _

lemma directSourceFinalModelMap_path : d.directSourceFinalModelMap R ≫
    HomotopyPullbackModel.path R _ _ =
      ((d.directSourceClassWitness R).reverse.comp (d.directInitialNativeWitness R)).hom :=
  HomotopyPullbackModel.lift_path R _ _ _ _ _

lemma fixedRightDirectModelMap_left : d.fixedRightDirectModelMap R ≫
    SquareZeroExtension.relativeLeft (d.rightClassifyingLayer R) (d.fixedRightCompletedClass R) =
    SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) :=
  SquareZeroExtension.classModelMap_left _ _ _ _

lemma fixedRightDirectModelMap_right : d.fixedRightDirectModelMap R ≫
    SquareZeroExtension.relativeRight (d.rightClassifyingLayer R) (d.fixedRightCompletedClass R) =
    SquareZeroExtension.relativeRight (d.denominatorLayer R) (d.sourceClass R) :=
  SquareZeroExtension.classModelMap_right _ _ _ _

lemma fixedRightCompletedClass_native : d.fixedRightCompletedClass R ≫
    d.rightDenominatorClassRestore R =
    d.fixedRightCompletedNativeSource R ≫ postnikovPerturbedClass R (B.obj j).obj n hn := by
  simpa only [fixedRightCompletedNativeSource, postnikovCellClass, Category.assoc] using
    d.fixedRightCompletedClass_restore R

lemma directSourceClassWitness_restore : (d.directSourceClassWitness R).hom =
    SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) ≫
      (d.fixedRightDirectWitness R).hom ≫ Path.map R (d.rightDenominatorClassRestore R) := by
  let L := SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R)
  let f' := postnikovPerturbedClass R (B.obj j).obj n hn
  let h₀ := SquareZeroExtension.sourceModelClassWitness_hom
    (directNativeLayer (n := n) (hn := hn) (B := B) (j := j) R) f' (d.directRelativeBase R)
    (d.directRelativeSourcePath R) (d.directRelativeSourcePath_class_relative R)
  let h₁ := Category.assoc L (d.fixedRightDirectSourceWitness R).hom (Path.map R f')
  let h₂ := congrArg (fun t => L ≫ t ≫ Path.map R f')
    (d.fixedRightDirectSourceWitness_hom R)
  let h₃ := congrArg (fun t => L ≫ t) (d.fixedRightDirectWitness_restore R).symm
  exact ((h₀.trans h₁).trans h₂).trans h₃

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
