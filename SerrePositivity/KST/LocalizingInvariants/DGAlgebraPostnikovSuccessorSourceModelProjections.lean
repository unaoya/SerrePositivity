module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassSourceModel

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

lemma sourceClass_baseChange : d.sourceClass R ≫
    SquareZero.baseChangeMap (d.lowerBaseInverse R).roof.denominator
      (postnikovShiftedLayerBimodule R (B.obj d.layerInverse.zero.stage).obj n hn 1) =
    d.sourceCellMap R ≫
      postnikovCellClass R (B.obj d.layerInverse.zero.stage).obj n hn := by
  rw [sourceClass, Category.assoc, postnikovCellClassOver_map]
  exact (Category.assoc _ _ _).symm

lemma sourceToOriginalModel_left : d.sourceToOriginalModel R ≫
    HomotopyPullbackModel.left R _ _ = HomotopyPullbackModel.left R _ _ ≫ d.sourceCellMap R ≫
      postnikovCellLift R (B.obj d.layerInverse.zero.stage).obj n hn := by
  rw [sourceToOriginalModel, Category.assoc, postnikovCellHomotopyPullbackComparison_left,
    ← Category.assoc]
  rw [sourceToCellModel, HomotopyPullbackModel.map_left, Category.assoc]

lemma sourceToOriginalModel_path : d.sourceToOriginalModel R ≫
    HomotopyPullbackModel.path R _ _ = HomotopyPullbackModel.path R _ _ ≫ Path.map R
      (SquareZero.baseChangeMap (d.lowerBaseInverse R).roof.denominator
        (postnikovShiftedLayerBimodule R (B.obj d.layerInverse.zero.stage).obj
          n hn 1)) := by
  rw [sourceToOriginalModel, Category.assoc, postnikovCellHomotopyPullbackComparison_path]
  exact HomotopyPullbackModel.map_path R _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
