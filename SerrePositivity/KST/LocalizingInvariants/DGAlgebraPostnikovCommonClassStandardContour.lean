module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardNaturalitySquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueSolved

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonClassViaBContourZero :=
  (postnikovCommonRightViaBContourPath R f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))
    (SquareZero.baseChangeMap_projection _ _)

lemma postnikovCommonClassStandardViaB_contour_hom :
    (postnikovCommonClassStandardViaBZeroRelative R f c d hj).hom =
      (postnikovCommonClassViaBContourZero R f c d hj).hom := rfl

def postnikovCommonClassStandardContourPath :=
  SquareZero.RelativeWitness.transferEndpoints
    (postnikovCommonClassStandardViaBZeroRelative R f c d hj)
    (postnikovCommonClassViaBContourZero R f c d hj)
    (postnikovCommonClassStandardViaB_contour_hom R f c d hj)
    (postnikovCommonClassStandardThenNaturality R f c d hj)

lemma postnikovCommonClassStandardContourPath_hom :
    (postnikovCommonClassStandardContourPath R f c d hj).hom =
      (postnikovCommonClassStandardThenNaturality R f c d hj).hom := rfl

def postnikovCommonClassStandardContourSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonClassStandardContourPath R f c d hj)
    (postnikovCommonClassViaBContourZero R f c d hj) :=
  (postnikovCommonClassStandardNaturalitySquare R f c d hj).reindex _ _ rfl
    (postnikovCommonClassStandardViaB_contour_hom R f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
