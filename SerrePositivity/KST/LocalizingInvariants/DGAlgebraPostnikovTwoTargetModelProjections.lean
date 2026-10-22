module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassTargetModel

/-!
概要：元の二切断候補の標的比較が保持する左脚と全経路を公開する。
方針：元の cell 模型射と摂動比較の二成分の式を合成する。
規約：元の targetToOriginalModel を保持。使われ方：元の fⱼ 後合成との厳密な比較。
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

lemma targetToOriginalModel_left : d.targetToOriginalModel R ≫
    HomotopyPullbackModel.left R _ _ = HomotopyPullbackModel.left R _ _ ≫
      d.targetCellMap R ≫ postnikovCellLift R (A.obj j).obj 1 (by omega) := by
  rw [targetToOriginalModel, Category.assoc, postnikovCellHomotopyPullbackComparison_left,
    ← Category.assoc]
  rw [targetToCellModel, HomotopyPullbackModel.map_left, Category.assoc]

lemma targetToOriginalModel_path : d.targetToOriginalModel R ≫
    HomotopyPullbackModel.path R _ _ = HomotopyPullbackModel.path R _ _ ≫ Path.map R
      (SquareZero.baseChangeMap (d.targetBase R)
        (postnikovShiftedLayerBimodule R (A.obj j).obj 1 (by omega) 1)) := by
  rw [targetToOriginalModel, Category.assoc, postnikovCellHomotopyPullbackComparison_path]
  exact HomotopyPullbackModel.map_path R _ _ _ _ _ _ _ _ _

lemma targetToOriginalModel_base : d.targetToOriginalModel R ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ ≫
      d.targetBase R := by
  rw [targetToOriginalModel, Category.assoc, postnikovCellHomotopyPullbackComparison_right]
  exact HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
