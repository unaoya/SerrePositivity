module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovStrictZeroBase

/-!
概要：零底の通常模型と経路模型を、元の有限切断射と両射影を保持して比較する。
方針：元の Postnikov 遷移の次数全射性を使い、元の厳密正方形の持ち上げを同定する。
規約：元の実比較射を使う。使われ方：有界な通常模型上での層と class の比較。
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

def postnikovStrictZeroComparison :
    LevelHom (postnikovStrictZeroBaseTower R f n hn) (postnikovZeroBaseTower R f n hn) :=
  strictComparison R (f.map (postnikovFunctor R 0)) (postnikovTransitionLevelHom R B n 0 hn)

lemma postnikovStrictZeroComparison_quasiIso (i : ℕ) :
    QuasiIso ((postnikovStrictZeroComparison R f n hn).app i).hom :=
  strictComparison_quasiIso_right R _ _
    (fun j => postnikovTransition_epi R (B.obj j).obj n 0 hn) i

lemma postnikovStrictZeroComparison_right :
    (postnikovStrictZeroComparison R f n hn).comp (postnikovZeroBaseProjection R f n hn) =
      postnikovStrictZeroBaseProjection R f n hn := strictComparison_comp_right R _ _

lemma postnikovStrictZeroComparison_left :
    (postnikovStrictZeroComparison R f n hn).comp
      (leftProjection R (f.map (postnikovFunctor R 0))
        (postnikovTransitionLevelHom R B n 0 hn)) =
      MonoidPullback.leftProjection (f.map (postnikovFunctor R 0))
        (postnikovTransitionLevelHom R B n 0 hn) := strictComparison_comp_left R _ _

lemma postnikovStrictZeroBaseLift_comparison :
    (postnikovStrictZeroBaseLift R f n hn).comp (postnikovStrictZeroComparison R f n hn) =
      postnikovZeroBaseLift R f n hn := strictComparison_squareLift R _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
