module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandardNaturalitySquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGlueSolved

/-!
概要：native 標準像と fⱼ の自然性の合成を、元の輪郭の端点表示へ厳密に移す。
方針：ViaB の全射が元の輪郭の全射と一致することから、二重経路の端点を移す。
規約：合成と二重経路の全射を変えない。使われ方：G の反転と元の W の接続。
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

def postnikovCommonClassViaBContourZero :=
  (postnikovCommonRightViaBContourPath R hn f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
    (SquareZero.baseChangeMap_projection _ _)

lemma postnikovCommonClassStandardViaB_contour_hom :
    (postnikovCommonClassStandardViaBZeroRelative R hn f c d hj).hom =
      (postnikovCommonClassViaBContourZero R hn f c d hj).hom := rfl

def postnikovCommonClassStandardContourPath :=
  SquareZero.RelativeWitness.transferEndpoints
    (postnikovCommonClassStandardViaBZeroRelative R hn f c d hj)
    (postnikovCommonClassViaBContourZero R hn f c d hj)
    (postnikovCommonClassStandardViaB_contour_hom R hn f c d hj)
    (postnikovCommonClassStandardThenNaturality R hn f c d hj)

lemma postnikovCommonClassStandardContourPath_hom :
    (postnikovCommonClassStandardContourPath R hn f c d hj).hom =
      (postnikovCommonClassStandardThenNaturality R hn f c d hj).hom := rfl

def postnikovCommonClassStandardContourSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonClassStandardContourPath R hn f c d hj)
    (postnikovCommonClassViaBContourZero R hn f c d hj) :=
  (postnikovCommonClassStandardNaturalitySquare R hn f c d hj).reindex _ _ rfl
    (postnikovCommonClassStandardViaB_contour_hom R hn f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
