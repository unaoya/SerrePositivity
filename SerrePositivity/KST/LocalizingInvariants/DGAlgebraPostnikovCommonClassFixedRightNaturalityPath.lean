module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedZeroComposition
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassGlueStandardBottom
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeFollowingTransfer

/-!
概要：元の native 標準経路に fⱼ の自然性を接合し、fixed class 互換性にも接合する。
方針：標準経路の全射同定から、後続自然性の接合端点と底を移す。
規約：native 経路の端点と全射を保持。使われ方：fixed class 自身の右三角形比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonClassFixedNaturalityEndpoint :
    postnikovCommonClassStandardGlueSource R f c d ⟶
      postnikovZeroClassTarget R (B.obj j).obj 1 1 :=
  (postnikovCommonRightImageToSecond R f c d ≫
    ((cellAugmentation R (cellResolution R (postnikovCommonClassBase R f c d)) ≫
      postnikovCellClassOver R (B.obj j).obj (postnikovCommonClassBase R f c d) 1 (by omega)
        (((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
          postnikovMap R (A.transition hj).hom 1) ≫ postnikovMap R (f.app j).hom 1)) ≫
      postnikovCommonRightViaAImageToZero R f c d hj)) ≫
    SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)

lemma postnikovCommonClassFixedStandard_reference_hom :
    (postnikovCommonClassStandardContourRelative R f c d hj).hom =
      (postnikovCommonClassFixedStandardMappedRelative R f c d hj).hom := by
  exact SquareZero.RelativeWitness.replaceHom_hom
    ((postnikovCommonRightViaAFirstZeroPath R f c d hj).mapOver
      (postnikovCommonRightClassifyingBase R f c d hj)
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))
      (SquareZero.baseChangeMap_projection _ _))
    (postnikovCommonClassFixedStandardMappedRelative R f c d hj).hom
    (postnikovCommonClassFixedStandardMapped_first_hom R f c d hj).symm

def postnikovCommonClassFixedRightNaturality : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R f c d ≫
      postnikovCommonClassFixedZeroBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
    ((cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R f c d) ≫
      postnikovCommonClassStandardEndpoint R f c d hj) ≫
      postnikovCommonClassFixedZeroMap R f c d hj)
    (postnikovCommonClassFixedNaturalityEndpoint R f c d hj) :=
  let v := postnikovCommonClassStandardContourRelative R f c d hj
  let v' := postnikovCommonClassFixedStandardMappedRelative R f c d hj
  let w := (postnikovCommonRightViaASecondZeroPath R f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))
    (SquareZero.baseChangeMap_projection _ _)
  SquareZero.RelativeWitness.followWithEndpoints
    (R := R) (B := postnikov R (B.obj j).obj 0)
    (W := postnikovCommonClassStandardGlueSource R f c d)
    (N := DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
    (q := postnikovCommonClassStandardGlueProjection R f c d ≫
      postnikovCommonRightClassifyingBase R f c d hj)
    (q' := postnikovCommonClassStandardGlueProjection R f c d ≫
      postnikovCommonClassFixedZeroBase R f c d hj) v v'
    (postnikovCommonClassFixedStandard_reference_hom R f c d hj) w

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
