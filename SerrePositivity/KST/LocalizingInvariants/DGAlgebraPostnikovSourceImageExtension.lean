module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageClass
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMap

/-!
概要：元の源上段から実係数像による拡大へ、実代数射を構成する。
方針：元の源の包含・遷移と、その厳密な class 等式による定数乗法的経路を持ち上げる。
規約：元の右脚を厳密に保持。使われ方：LT の連結な像因子分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

abbrev postnikovSourceImageExtension := HomotopyPullbackModel.algebra R
  (postnikovSourceImageClass R f n hn)
  (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1))

def postnikovSourceImageFactorWitness : Path.Witness R
    (postnikovPerturbedInclusion R B n hn ≫ postnikovSourceImageClass R f n hn)
    (postnikovTransition R B (n + 1) n (by omega) ≫
      SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1)) where
  hom := postnikovPerturbedInclusion R B n hn ≫ postnikovSourceImageClass R f n hn ≫
    Path.diagonal R _
  source_eq := by rw [Category.assoc, Category.assoc, Path.diagonal_source, Category.comp_id]
  target_eq := by
    rw [Category.assoc, Category.assoc, Path.diagonal_target, Category.comp_id]
    exact postnikovPerturbedInclusion_sourceImageClass R f n hn

def postnikovSourceImageFactor : postnikov R B (n + 1) ⟶
    postnikovSourceImageExtension R f n hn :=
  HomotopyPullbackModel.lift R _ _ (postnikovPerturbedInclusion R B n hn)
    (postnikovTransition R B (n + 1) n (by omega)) (postnikovSourceImageFactorWitness R f n hn)

lemma postnikovSourceImageFactor_left : postnikovSourceImageFactor R f n hn ≫
    HomotopyPullbackModel.left R _ _ = postnikovPerturbedInclusion R B n hn :=
  HomotopyPullbackModel.lift_left R _ _ _ _ _

lemma postnikovSourceImageFactor_right : postnikovSourceImageFactor R f n hn ≫
    HomotopyPullbackModel.right R _ _ = postnikovTransition R B (n + 1) n (by omega) :=
  HomotopyPullbackModel.lift_right R _ _ _ _ _

lemma postnikovSourceImageFactor_path : postnikovSourceImageFactor R f n hn ≫
    HomotopyPullbackModel.path R _ _ =
      postnikovPerturbedInclusion R B n hn ≫ postnikovSourceImageClass R f n hn ≫
        Path.diagonal R _ := HomotopyPullbackModel.lift_path R _ _ _ _ _

def postnikovSourceImageToTarget : postnikovSourceImageExtension R f n hn ⟶
    HomotopyPullbackModel.algebra R (postnikovPerturbedClass R C n hn)
      (SquareZero.zeroSection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1)) :=
  HomotopyPullbackModel.map R _ _ _ _ (postnikovPerturbedMap R f n hn)
    (postnikovImageClassTargetMap R f n hn) (postnikovMap R f n)
    (postnikovSourceImageClass_inclusion R f n hn).symm
    (SquareZero.zeroSection_mapOver _ _ _ _).symm

lemma postnikovSourceImageToTarget_left : postnikovSourceImageToTarget R f n hn ≫
    HomotopyPullbackModel.left R _ _ =
      HomotopyPullbackModel.left R _ _ ≫ postnikovPerturbedMap R f n hn :=
  HomotopyPullbackModel.map_left R _ _ _ _ _ _ _ _ _

lemma postnikovSourceImageToTarget_right : postnikovSourceImageToTarget R f n hn ≫
    HomotopyPullbackModel.right R _ _ =
      HomotopyPullbackModel.right R _ _ ≫ postnikovMap R f n :=
  HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _

lemma postnikovSourceImageToTarget_path : postnikovSourceImageToTarget R f n hn ≫
    HomotopyPullbackModel.path R _ _ = HomotopyPullbackModel.path R _ _ ≫
      Path.map R (postnikovImageClassTargetMap R f n hn) :=
  HomotopyPullbackModel.map_path R _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
