module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageSquareZeroLaws
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSourceImageExtension

/-!
概要：元の可換正方形を、源側像拡大の元の二脚・乗法的経路を保つ実代数射へ送る。
方針：元の摂動源・像の平方零代数・源の下段の実三成分を模型射へ渡す。
規約：同じ底と同じ係数像を使用。使われ方：源側像拡大の実図式と塔の遷移。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C B' C' : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [B'.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)
  (f : B ⟶ C) (f' : B' ⟶ C') (s : B ⟶ B') (t : C ⟶ C') (h : f ≫ t = s ≫ f')

def postnikovSourceImageExtensionSquareMap : postnikovSourceImageExtension R f n hn ⟶
    postnikovSourceImageExtension R f' n hn :=
  HomotopyPullbackModel.map R _ _ _ _ (postnikovPerturbedMap R s n hn)
    (postnikovSourceImageSquareZeroMap R n hn f f' s t h) (postnikovMap R s n)
    (postnikovSourceImageClass_square R n hn f f' s t h)
    (postnikovSourceImageSquareZeroMap_zeroSection R n hn f f' s t h)

lemma postnikovSourceImageExtensionSquareMap_left :
    postnikovSourceImageExtensionSquareMap R n hn f f' s t h ≫
      HomotopyPullbackModel.left R _ _ =
        HomotopyPullbackModel.left R _ _ ≫ postnikovPerturbedMap R s n hn :=
  HomotopyPullbackModel.map_left R _ _ _ _ _ _ _ _ _

lemma postnikovSourceImageExtensionSquareMap_right :
    postnikovSourceImageExtensionSquareMap R n hn f f' s t h ≫
      HomotopyPullbackModel.right R _ _ =
        HomotopyPullbackModel.right R _ _ ≫ postnikovMap R s n :=
  HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _

lemma postnikovSourceImageExtensionSquareMap_path :
    postnikovSourceImageExtensionSquareMap R n hn f f' s t h ≫
      HomotopyPullbackModel.path R _ _ = HomotopyPullbackModel.path R _ _ ≫
        Path.map R (postnikovSourceImageSquareZeroMap R n hn f f' s t h) :=
  HomotopyPullbackModel.map_path R _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
