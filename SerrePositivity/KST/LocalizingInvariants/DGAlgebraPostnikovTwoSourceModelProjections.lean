module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassSourceModel

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorSourceModelProjections

/-!
概要：元の源 class の底変更式と、元の source 模型比較の左脚・全経路を公開する。
方針：元の cell class の底変更と、同じ cell 模型射の成分式を合成する。
規約：元の sourceToOriginalModel を保持。使われ方：直接 B 遷移の模型経路。
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

lemma sourceClass_baseChange : d.sourceClass R ≫
    SquareZero.baseChangeMap (d.lowerBaseInverse R).roof.denominator
      (postnikovShiftedLayerBimodule R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) 1) =
    d.sourceCellMap R ≫
      postnikovCellClass R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) :=
  PostnikovSuccessorClassInverseData.sourceClass_baseChange
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToOriginalModel_left : d.sourceToOriginalModel R ≫
    HomotopyPullbackModel.left R _ _ = HomotopyPullbackModel.left R _ _ ≫ d.sourceCellMap R ≫
      postnikovCellLift R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) :=
  PostnikovSuccessorClassInverseData.sourceToOriginalModel_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToOriginalModel_path : d.sourceToOriginalModel R ≫
    HomotopyPullbackModel.path R _ _ = HomotopyPullbackModel.path R _ _ ≫ Path.map R
      (SquareZero.baseChangeMap (d.lowerBaseInverse R).roof.denominator
        (postnikovShiftedLayerBimodule R (B.obj d.layerInverse.zero.stage).obj
          1 (by omega) 1)) :=
  PostnikovSuccessorClassInverseData.sourceToOriginalModel_path
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
