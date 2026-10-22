module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageClassComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMap

/-!
概要：実係数像の class による拡大模型と、元の標的係数への実模型射を構成する。
方針：元の包含と底比較を cospan の三つの実射へ渡す。
規約：元の底への右脚を保持。この射の準同型性は要求しない。使われ方：像拡大の比較。
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

abbrev postnikovImageExtension := HomotopyPullbackModel.algebra R (postnikovImageClass R f n hn)
  (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1))

abbrev postnikovImageIncludedExtension := HomotopyPullbackModel.algebra R
  (postnikovImageClass R f n hn ≫ postnikovImageClassTargetMap R f n hn)
  (SquareZero.zeroSection (postnikov R C n) (postnikovShiftedLayerBimodule R C n hn 1))

def postnikovImageExtensionMap : postnikovImageExtension R f n hn ⟶
    postnikovImageIncludedExtension R f n hn :=
  HomotopyPullbackModel.map R _ _ _ _ (𝟙 _) (postnikovImageClassTargetMap R f n hn)
    (postnikovMap R f n) (by simp)
    (SquareZero.zeroSection_mapOver _ _ _ _).symm

lemma postnikovImageExtensionMap_right : postnikovImageExtensionMap R f n hn ≫
    HomotopyPullbackModel.right R _ _ =
      HomotopyPullbackModel.right R _ _ ≫ postnikovMap R f n :=
  HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _

lemma postnikovImageExtensionMap_left : postnikovImageExtensionMap R f n hn ≫
    HomotopyPullbackModel.left R _ _ = HomotopyPullbackModel.left R _ _ :=
  (HomotopyPullbackModel.map_left R _ _ _ _ _ _ _ _ _).trans (Category.comp_id _)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
