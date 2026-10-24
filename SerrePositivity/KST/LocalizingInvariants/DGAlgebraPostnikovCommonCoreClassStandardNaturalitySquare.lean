module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandardComposite
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareMapOver
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareReindex
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeEndpointTransfer

/-!
概要：元の標準経路像と fⱼ の自然性の合成を、ViaB と実二重経路で比較する。
方針：元の ViaA→ViaB の二重経路を零 class 標的へ写し、全射同定で表示を移す。
規約：元の Γ 射影・両端と全二重経路を保持。使われ方：fixed 右 class 三角形。
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

def postnikovCommonClassStandardViaAZeroRelative :=
  (postnikovCommonRightZeroAffineViaA R hn f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
    (SquareZero.baseChangeMap_projection _ _)

def postnikovCommonClassStandardViaBRawZeroRelative :=
  (postnikovCommonRightZeroAffineViaB R hn f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
    (SquareZero.baseChangeMap_projection _ _)

def postnikovCommonClassStandardViaBZeroRelative :=
  SquareZero.RelativeWitness.transferEndpoints
    (postnikovCommonClassStandardViaAZeroRelative R hn f c d hj)
    (postnikovCommonClassStandardThenNaturality R hn f c d hj)
    (postnikovCommonClassStandardThenNaturality_hom R hn f c d hj).symm
    (postnikovCommonClassStandardViaBRawZeroRelative R hn f c d hj)

def postnikovCommonClassStandardNaturalitySquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonClassStandardThenNaturality R hn f c d hj)
    (postnikovCommonClassStandardViaBZeroRelative R hn f c d hj) := by
  let h := (postnikovCommonRightZeroAffineSquare R hn f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
    (SquareZero.baseChangeMap_projection _ _)
  exact h.reindex _ _ (postnikovCommonClassStandardThenNaturality_hom R hn f c d hj).symm rfl

def postnikovCommonClassStandardNaturalityTransportHomotopy :=
  SquareZeroExtension.transportHomotopy _
    (postnikovCommonClassStandardNaturalitySquare R hn f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
