module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightImageRestore
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassModelMap

/-!
概要：fixed の fⱼ 係数像の模型から、元の Bⱼ の摂動 class 模型への実射を構成する。
方針：係数復元と元の cell 比較・摂動自然性を、同じ実 cospan 射にする。
規約：元の fⱼ と元の二脚を保持。使われ方：fixed roof の標的比較の回収。
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

lemma targetClass_baseChange : d.targetClass R ≫ SquareZero.baseChangeMap (d.targetBase R)
    (postnikovShiftedLayerBimodule R (A.obj j).obj 1 (by omega) 1) =
    d.targetCellMap R ≫ postnikovCellClass R (A.obj j).obj 1 (by omega) := by
  let α := postnikovCommonClassCompatibilityToCell R f d.baseInverse d.layerInverse
  change (α ≫ postnikovCellClassOver R (A.obj j).obj (d.classBase R) 1 (by omega)
    (d.targetBase R)) ≫ _ = (α ≫ cellResolutionMap R (d.targetBase R)) ≫ _
  rw [Category.assoc, postnikovCellClassOver_map, Category.assoc]

def rightImageNativeSource := d.targetCellMap R ≫
  postnikovCellLift R (A.obj j).obj 1 (by omega) ≫
    postnikovPerturbedMap R (f.app j).hom 1 (by omega)

lemma rightImageClass_restore : d.rightImageClass R ≫ d.rightImageClassRestore R =
    d.rightImageNativeSource R ≫ postnikovPerturbedClass R (B.obj j).obj 1 (by omega) := by
  rw [rightImageClass, Category.assoc, d.rightTargetCoefficient_restore R,
    ← Category.assoc, d.targetClass_baseChange R]
  simp only [rightImageNativeSource, postnikovCellClass, Category.assoc,
    postnikovPerturbedClass_naturality]

def rightImageToOriginalModel :
    SquareZeroExtension.model (d.rightClassifyingLayer R) (d.rightImageClass R) ⟶
      postnikovClassModel R (B.obj j).obj 1 (by omega) :=
  HomotopyPullbackModel.map R (d.rightImageClass R) _
    (postnikovPerturbedClass R (B.obj j).obj 1 (by omega)) _
    (d.rightImageNativeSource R) (d.rightImageClassRestore R)
    (postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le)
    (d.rightImageClass_restore R).symm
    (SquareZero.coefficientRestore_zeroSection _ _ _).symm

lemma rightImageToOriginalModel_left : d.rightImageToOriginalModel R ≫
    HomotopyPullbackModel.left R _ _ =
      HomotopyPullbackModel.left R _ _ ≫
        d.rightImageNativeSource R := HomotopyPullbackModel.map_left R _ _ _ _ _ _ _ _ _

lemma rightImageToOriginalModel_right : d.rightImageToOriginalModel R ≫
    HomotopyPullbackModel.right R _ _ =
      HomotopyPullbackModel.right R _ _ ≫
        postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le :=
  HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _

lemma rightImageToOriginalModel_path : d.rightImageToOriginalModel R ≫
    HomotopyPullbackModel.path R _ _ =
      HomotopyPullbackModel.path R _ _ ≫
        Path.map R (d.rightImageClassRestore R) :=
  HomotopyPullbackModel.map_path R _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
