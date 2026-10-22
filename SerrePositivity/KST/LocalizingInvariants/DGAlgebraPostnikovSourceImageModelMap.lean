module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassLayerHomology

/-!
概要：元の源 class 模型から源側像拡大への実射を構成し、元の源上段射を回収する。
方針：係数像への射影を模型射に送り、二脚と定数乗法的経路で比較する。
規約：元の source factor と厳密に一致。使われ方：層の像射影との整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

def postnikovSourceImageModelMap : postnikovClassModel R B n hn ⟶
    postnikovSourceImageExtension R f n hn :=
  SquareZeroExtension.map (postnikovShiftedLayerBimodule R B n hn 1)
    (postnikovShiftedLayerImage R f n hn 1) (postnikovPerturbedClass R B n hn)
    (postnikovSourceImageClass R f n hn) (𝟙 _) (𝟙 _)
    (postnikovSourceImageCoefficientMap R f n hn)
    (postnikovShiftedLayerImageProjection R f n hn 1).hom rfl
    (by simp [postnikovSourceImageClass])

lemma postnikovSourceImageModelMap_left : postnikovSourceImageModelMap R f n hn ≫
    HomotopyPullbackModel.left R _ _ = HomotopyPullbackModel.left R _ _ :=
  (HomotopyPullbackModel.map_left R _ _ _ _ _ _ _ _ _).trans (Category.comp_id _)

lemma postnikovSourceImageModelMap_right : postnikovSourceImageModelMap R f n hn ≫
    HomotopyPullbackModel.right R _ _ = HomotopyPullbackModel.right R _ _ :=
  (HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _).trans (Category.comp_id _)

lemma postnikovSourceImageModelMap_path : postnikovSourceImageModelMap R f n hn ≫
    HomotopyPullbackModel.path R _ _ = HomotopyPullbackModel.path R _ _ ≫
      Path.map R (postnikovSourceImageCoefficientMap R f n hn) :=
  HomotopyPullbackModel.map_path R _ _ _ _ _ _ _ _ _

lemma postnikovSourceImageModelMap_comparison : postnikovHomotopyPullbackComparison R B n hn ≫
    postnikovSourceImageModelMap R f n hn = postnikovSourceImageFactor R f n hn := by
  apply HomotopyPullbackModel.hom_ext R (postnikovSourceImageClass R f n hn)
    (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1))
  · rw [Category.assoc, postnikovSourceImageModelMap_left,
      postnikovHomotopyPullbackComparison_left, postnikovSourceImageFactor_left]
  · rw [Category.assoc, postnikovSourceImageModelMap_right,
      postnikovHomotopyPullbackComparison_right, postnikovSourceImageFactor_right]
  · rw [Category.assoc, postnikovSourceImageModelMap_path, ← Category.assoc,
      postnikovHomotopyPullbackComparison_path, postnikovSourceImageFactor_path]
    simp only [Category.assoc, Path.diagonal_naturality, postnikovSourceImageClass]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
