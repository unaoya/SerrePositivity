module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedZeroComposition
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassGlueStandardBottom
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonClassFixedNaturalityEndpoint :
    postnikovCommonClassStandardGlueSource R hn f c d ⟶
      postnikovZeroClassTarget R (B.obj j).obj n 1 :=
  (postnikovCommonRightImageToSecond R hn f c d ≫
    ((cellAugmentation R (cellResolution R (postnikovCommonClassBase R hn f c d)) ≫
      postnikovCellClassOver R (B.obj j).obj (postnikovCommonClassBase R hn f c d) n hn
        (((roofRefine R hn f c d.zero.source_le).roof.numerator ≫
          postnikovMap R (A.transition hj).hom n) ≫ postnikovMap R (f.app j).hom n)) ≫
      postnikovCommonRightViaAImageToZero R hn f c d hj)) ≫
    SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)

lemma postnikovCommonClassFixedStandard_reference_hom :
    (postnikovCommonClassStandardContourRelative R hn f c d hj).hom =
      (postnikovCommonClassFixedStandardMappedRelative R hn f c d hj).hom := by
  exact SquareZero.RelativeWitness.replaceHom_hom
    ((postnikovCommonRightViaAFirstZeroPath R hn f c d hj).mapOver
      (postnikovCommonRightClassifyingBase R hn f c d hj)
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
      (SquareZero.baseChangeMap_projection _ _))
    (postnikovCommonClassFixedStandardMappedRelative R hn f c d hj).hom
    (postnikovCommonClassFixedStandardMapped_first_hom R hn f c d hj).symm

def postnikovCommonClassFixedRightNaturality : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R hn f c d ≫
      postnikovCommonClassFixedZeroBase R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
    ((cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d) ≫
      postnikovCommonClassStandardEndpoint R hn f c d hj) ≫
      postnikovCommonClassFixedZeroMap R hn f c d hj)
    (postnikovCommonClassFixedNaturalityEndpoint R hn f c d hj) :=
  let v := postnikovCommonClassStandardContourRelative R hn f c d hj
  let v' := postnikovCommonClassFixedStandardMappedRelative R hn f c d hj
  let w := (postnikovCommonRightViaASecondZeroPath R hn f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
    (SquareZero.baseChangeMap_projection _ _)
  SquareZero.RelativeWitness.followWithEndpoints
    (R := R) (B := postnikov R (B.obj j).obj 0)
    (W := postnikovCommonClassStandardGlueSource R hn f c d)
    (N := DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
    (q := postnikovCommonClassStandardGlueProjection R hn f c d ≫
      postnikovCommonRightClassifyingBase R hn f c d hj)
    (q' := postnikovCommonClassStandardGlueProjection R hn f c d ≫
      postnikovCommonClassFixedZeroBase R hn f c d hj) v v'
    (postnikovCommonClassFixedStandard_reference_hom R hn f c d hj) w

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
