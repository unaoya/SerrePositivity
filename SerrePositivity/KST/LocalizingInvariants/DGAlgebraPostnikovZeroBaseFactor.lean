module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroBaseChange
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackSquareLift

/-!
概要：元の有限 Postnikov 射を、零切断を底に持つ実経路模型を通して因子分解する。
方針：切断の元の自然性の正方形を対角経路で持ち上げ、元の二射の合成を保持する。
規約：正次数の連結度・逆は別工程。使われ方：底を揃えた層の実比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)}
  (f : LevelHom A B) (n : ℤ) (hn : 0 ≤ n)

lemma postnikovZeroBase_square :
    (postnikovTransitionLevelHom R A n 0 hn).comp (f.map (postnikovFunctor R 0)) =
      (f.map (postnikovFunctor R n)).comp (postnikovTransitionLevelHom R B n 0 hn) := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact (postnikovTransition_naturality R (A.obj i).obj (f.app i).hom n 0 hn).symm

/-- 元の有限切断から底を揃えた元の経路模型への実射。 -/
def postnikovZeroBaseLift :
    LevelHom (A.map (postnikovFunctor R n)) (postnikovZeroBaseTower R f n hn) :=
  squareLift R (f.map (postnikovFunctor R 0)) (postnikovTransitionLevelHom R B n 0 hn)
    (postnikovTransitionLevelHom R A n 0 hn) (f.map (postnikovFunctor R n))
    (postnikovZeroBase_square R f n hn)

lemma postnikovZeroBase_fac :
    (postnikovZeroBaseLift R f n hn).comp (postnikovZeroBaseProjection R f n hn) =
      f.map (postnikovFunctor R n) :=
  squareLift_comp_right R _ _ _ _ _

lemma postnikovZeroBaseLift_left :
    (postnikovZeroBaseLift R f n hn).comp
      (leftProjection R (f.map (postnikovFunctor R 0))
        (postnikovTransitionLevelHom R B n 0 hn)) = postnikovTransitionLevelHom R A n 0 hn :=
  squareLift_comp_left R _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
