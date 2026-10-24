module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectFinalProjections

/-!
概要：source 模型経路の終点の全経路を、元の直接 class 模型射の全経路へ同定する。
方針：元の終点 class・全 source class 経路・元の模型経路の三項を同時に比較する。
規約：元の全経路の等式。使われ方：終点模型射の厳密な同定。
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

lemma directSourceFinalModelMap_path_fixed : d.directSourceFinalModelMap R ≫
    HomotopyPullbackModel.path R _ _ =
    d.fixedRightDirectModelMap R ≫
      SquareZeroExtension.relativePath (d.rightClassifyingLayer R) (d.fixedRightCompletedClass R) ≫
        Path.map R (d.rightDenominatorClassRestore R) := by
  rw [d.directSourceFinalModelMap_path R]
  let M := d.denominatorLayer R
  let a := d.sourceClass R
  let N := d.rightClassifyingLayer R
  let b := d.fixedRightCompletedClass R
  let m := d.rightDenominatorCoefficient R
  let v := d.fixedRightDirectWitness R
  let k := d.rightDenominatorClassRestore R
  let f' := postnikovPerturbedClass R (B.obj j).obj n hn
  let L := SquareZeroExtension.relativeLeft M a
  have hp : L ≫ b ≫ k = (L ≫ d.fixedRightCompletedNativeSource R) ≫ f' := by
    simpa only [Category.assoc] using
      congrArg (fun t => L ≫ t) (d.fixedRightCompletedClass_native R)
  let h := SquareZeroExtension.classModelMap_path_post_of_witness m a b v
    (directNativeLayer (n := n) (hn := hn) (B := B) (j := j) R) k
    (d.directSourceClassWitness R) (d.directInitialNativeWitness R) hp
    (d.directSourceClassWitness_restore R).symm (d.directInitialNativeWitness_hom R).symm
  exact h.trans (Category.assoc _ _ _)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
