module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageFactorisationFunctor

/-!
概要：元の標的上段までの実因子分解の正方形射と、元の二脚・経路との整合を供給する。
方針：自然な二つの cospan 射を実模型射へ渡す。
規約：矢印関手の射と同じ実射。使われ方：元の source・target の実自然変換。
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

def postnikovImageFactorisationSquareMap : postnikovImageFactorisationObject R f n hn ⟶
    postnikovImageFactorisationObject R f' n hn :=
  HomotopyPullbackModel.map R _ _ _ _
    (postnikovSourceImageExtensionSquareMap R n hn f f' s t h)
    (postnikovClassModelMap R n hn t) (postnikovMap R t (n + 1))
    (postnikovSourceImageToTarget_square R n hn f f' s t h).symm
    (postnikovHomotopyPullbackComparison_square R n hn t)

lemma postnikovImageFactorisationSquareMap_comparison :
    postnikovImageFactorisationSquareMap R n hn f f' s t h ≫
      postnikovImageFactorisationComparison R f' n hn =
        postnikovImageFactorisationComparison R f n hn ≫
          postnikovSourceImageExtensionSquareMap R n hn f f' s t h :=
  HomotopyPullbackModel.map_left R _ _ _ _ _ _ _ _ _

lemma postnikovImageFactorisationSquareMap_target :
    postnikovImageFactorisationSquareMap R n hn f f' s t h ≫
      postnikovImageFactorisationTarget R f' n hn =
        postnikovImageFactorisationTarget R f n hn ≫ postnikovMap R t (n + 1) :=
  HomotopyPullbackModel.map_right R _ _ _ _ _ _ _ _ _

lemma postnikovImageFactorisationSquareMap_path :
    postnikovImageFactorisationSquareMap R n hn f f' s t h ≫
      HomotopyPullbackModel.path R _ _ = HomotopyPullbackModel.path R _ _ ≫
        Path.map R (postnikovClassModelMap R n hn t) :=
  HomotopyPullbackModel.map_path R _ _ _ _ _ _ _ _ _

lemma postnikovImageFactorisationArrowFunctor_map {f g : Arrow (NonpositiveAlgebra R)}
    (a : f ⟶ g) : (postnikovImageFactorisationArrowFunctor R n hn).map a =
      postnikovImageFactorisationSquareMap R n hn f.hom.hom g.hom.hom a.left.hom a.right.hom
        (postnikovSourceImageArrow_condition R a) := rfl

lemma postnikovImageFactorisationSource_path : postnikovImageFactorisationSource R f n hn ≫
    HomotopyPullbackModel.path R _ _ = postnikovSourceImageFactor R f n hn ≫
      postnikovSourceImageToTarget R f n hn ≫ Path.diagonal R _ :=
  HomotopyPullbackModel.lift_path R _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
