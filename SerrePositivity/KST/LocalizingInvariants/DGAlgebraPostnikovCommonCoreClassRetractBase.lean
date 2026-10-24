module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassRetract

/-!
概要：遷移後の二 class の経路を、元の共通底上へ実際に戻す。
方針：係数逆の底の左三角形で零底を元の A の遷移に同定し、底変更の経路を適用する。
規約：元の分子・遷移と各次数全射準同型の源射影を保持。使われ方：新しい class の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R n f j i hj)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonClassRetractBase : postnikovCommonClassBase R hn f c d ⟶
    postnikov R (A.obj j).obj n :=
  (roofRefine R hn f c d.zero.source_le).roof.numerator ≫
    postnikovMap R (A.transition hj).hom n

lemma postnikovCommonClassRetractBase_zero : postnikovCommonRightZeroBase R hn f c d ≫ e.base =
    postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
      postnikovTransition R (A.obj j).obj n 0 (by omega) := by
  rw [postnikovCommonRightZeroBase_source, Category.assoc, Category.assoc, e.left_base,
    postnikovCommonClassRetractBase, Category.assoc, postnikovTransition_naturality]

include e in
lemma postnikovCommonClassRetractTarget_projection :
    postnikovCommonClassRetractTarget R hn f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonRightZeroGlueProjection R hn f c d ≫
        (postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
          postnikovTransition R (A.obj j).obj n 0 (by omega)) := by
  rw [← postnikovCommonRightGlueTarget_retract R hn f c d e, Category.assoc,
    postnikovCommonRightRetract_projection, ← Category.assoc,
    postnikovCommonRightGlueTarget_projection,
    postnikovCommonClassRetractBase_zero R hn f c d e]

include e in
lemma postnikovCommonClassRetractSource_projection :
    postnikovCommonClassRetractSource R hn f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonRightZeroGlueProjection R hn f c d ≫
        (postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
          postnikovTransition R (A.obj j).obj n 0 (by omega)) := by
  rw [← postnikovCommonRightGlueSource_retract R hn f c d e, Category.assoc,
    postnikovCommonRightRetract_projection, ← Category.assoc,
    postnikovCommonRightGlueSource_projection,
    postnikovCommonClassRetractBase_zero R hn f c d e]

def postnikovCommonClassRetractLeft := SquareZero.baseChangeLift
  (postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
    postnikovTransition R (A.obj j).obj n 0 (by omega))
  (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (A.obj j).obj n) 1)
  (postnikovCommonRightZeroGlueProjection R hn f c d)
  (postnikovCommonClassRetractTarget R hn f c d (hj := hj))
  (postnikovCommonClassRetractTarget_projection R hn f c d e)

def postnikovCommonClassRetractRight := SquareZero.baseChangeLift
  (postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
    postnikovTransition R (A.obj j).obj n 0 (by omega))
  (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (A.obj j).obj n) 1)
  (postnikovCommonRightZeroGlueProjection R hn f c d)
  (postnikovCommonClassRetractSource R hn f c d (hj := hj))
  (postnikovCommonClassRetractSource_projection R hn f c d e)

def postnikovCommonClassRetractRelativeWitness : Path.Witness R
    (postnikovCommonClassRetractLeft R hn f c d e) (postnikovCommonClassRetractRight R hn f c d e) :=
  SquareZero.baseChangeWitness _ _ _ _ _ _ _ (postnikovCommonClassRetractWitness R hn f c d e)
    (by
      rw [postnikovCommonClassRetractWitness_projection,
        postnikovCommonClassRetractBase_zero R hn f c d e]
      simp only [Category.assoc])

lemma postnikovCommonClassRetractRelativeWitness_projection :
    (postnikovCommonClassRetractRelativeWitness R hn f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) = postnikovCommonRightZeroGlueProjection R hn f c d ≫
        Path.diagonal R (postnikovCommonClassBase R hn f c d) :=
  SquareZero.baseChangeWitness_relative _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
