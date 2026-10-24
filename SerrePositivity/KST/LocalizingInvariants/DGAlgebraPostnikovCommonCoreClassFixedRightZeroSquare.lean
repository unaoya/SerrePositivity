module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightBottom
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassRightZeroSquare

/-!
概要：元の fixed class 互換性に自然性と W を接いだ経路を、分母自然性と実比較する。
方針：元の native 合成の全射の同定に沿い、分母比較の両端と底を移す。
規約：元の native 経路・Γ・W・全二重経路を保持。使われ方：右模型三角形の復元。
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
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)
  (e : PostnikovZeroLayerInverse R n f j i hj)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonClassFixedRightDenominatorPath :=
  SquareZero.RelativeWitness.transferEndpoints
    (postnikovCommonClassGlueStandardBottom R hn f c d hj)
    (postnikovCommonClassFixedRightCompletedPath R hn f c d hj e)
    (postnikovCommonClassFixedRightCompletedPath_hom R hn f c d hj e).symm
    (postnikovCommonClassDenContourZero R hn f c d hj)

def postnikovCommonClassFixedRightZeroSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonClassFixedRightDenominatorPath R hn f c d hj e)
    (postnikovCommonClassFixedRightCompletedPath R hn f c d hj e) :=
  (postnikovCommonClassRightZeroSquare R hn f c d hj).reindex _ _ rfl
    (postnikovCommonClassFixedRightCompletedPath_hom R hn f c d hj e).symm

def postnikovCommonClassFixedRightZeroTransportHomotopy :=
  SquareZeroExtension.transportHomotopy _
    (postnikovCommonClassFixedRightZeroSquare R hn f c d hj e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
