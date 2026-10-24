module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectFinalProjections

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectFinalPathComparison

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma directSourceFinalModelMap_path_fixed : d.directSourceFinalModelMap R ≫
    HomotopyPullbackModel.path R _ _ =
    d.fixedRightDirectModelMap R ≫
      SquareZeroExtension.relativePath (d.rightClassifyingLayer R) (d.fixedRightCompletedClass R) ≫
        Path.map R (d.rightDenominatorClassRestore R) :=
  PostnikovSuccessorClassInverseData.directSourceFinalModelMap_path_fixed
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
