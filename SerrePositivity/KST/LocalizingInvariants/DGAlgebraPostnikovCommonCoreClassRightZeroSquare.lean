module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassGlueViaBMap
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareComposition

/-!
概要：分母自然性の零底像を、G⁻¹・native 標準自然性・元の W の実合成と比較する。
方針：元の分母比較と、G⁻¹ を前置し W を後置した標準比較を縦合成する。
規約：元の Γ・G・W・両端と底射影を保持。使われ方：fixed 右模型三角形への接続。
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

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonClassDenContourZero :=
  (postnikovCommonRightDenContourPath R hn f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
    (SquareZero.baseChangeMap_projection _ _)

def postnikovCommonClassRightZeroSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonClassDenContourZero R hn f c d hj)
    (postnikovCommonClassGlueStandardBottom R hn f c d hj) := by
  let h := (postnikovCommonRightGlueSolvedZeroSquare R hn f c d hj).replacePaths
    (v' := postnikovCommonClassDenContourZero R hn f c d hj)
    (w' := postnikovCommonClassGlueViaBBottom R hn f c d hj) rfl
    (postnikovCommonClassGlueViaB_map_hom R hn f c d hj)
  exact h.trans (postnikovCommonClassGlueStandardBottomSquare R hn f c d hj).symm

def postnikovCommonClassRightZeroTransportHomotopy :=
  SquareZeroExtension.transportHomotopy _ (postnikovCommonClassRightZeroSquare R hn f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
