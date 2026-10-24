module

public import
SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightNaturalityPath

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

def postnikovCommonClassFixedStandardNaturality : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R hn f c d ≫
      postnikovCommonClassFixedZeroBase R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
    ((cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d) ≫
      postnikovCommonClassTransitionTarget R hn f c d (hj := hj)) ≫
      postnikovCommonClassFixedZeroMap R hn f c d hj)
    (postnikovCommonClassFixedNaturalityEndpoint R hn f c d hj) :=
  (postnikovCommonClassFixedStandardMappedRelative R hn f c d hj).comp
    (postnikovCommonClassFixedRightNaturality R hn f c d hj)

lemma postnikovCommonClassFixedStandardNaturality_hom :
    (postnikovCommonClassFixedStandardNaturality R hn f c d hj).hom =
      (postnikovCommonClassStandardContourPath R hn f c d hj).hom := by
  let w := (postnikovCommonRightViaASecondZeroPath R hn f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
    (SquareZero.baseChangeMap_projection _ _)
  have h := SquareZero.RelativeWitness.followWithEndpoints_comp_hom
    (R := R) (B := postnikov R (B.obj j).obj 0)
    (W := postnikovCommonClassStandardGlueSource R hn f c d)
    (N := DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
    (postnikovCommonClassStandardContourRelative R hn f c d hj)
    (postnikovCommonClassFixedStandardMappedRelative R hn f c d hj)
    (postnikovCommonClassFixedStandard_reference_hom R hn f c d hj) w
  exact h.trans (postnikovCommonClassStandardContourPath_hom R hn f c d hj).symm

variable (e : PostnikovZeroLayerInverse R n f j i hj)

def postnikovCommonClassFixedCompatibilityNaturality : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R hn f c d ≫
      postnikovCommonClassFixedZeroBase R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
    ((cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d) ≫
      postnikovCommonClassTransitionSource R hn f c d (hj := hj)) ≫
      postnikovCommonClassFixedZeroMap R hn f c d hj)
    (postnikovCommonClassFixedNaturalityEndpoint R hn f c d hj) :=
  (postnikovCommonClassFixedCompatibilityMappedRelative R hn f c d hj e).comp
    (postnikovCommonClassFixedRightNaturality R hn f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
