module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightFixedBasePath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroNormalize
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessPrecomp

/-!
概要：指定右経路を保つ中央経路を、両側の class 自然性と同じ源上で affine 貼合せする。
方針：共通零底への三経路を相対証人へ束ね、同じ源の合成と反転を使う。
規約：追加の cell 合成は使わず全経路の線形公式を保つ。使われ方：整合する Γ class。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

local instance fixedGlue_zero_lower : (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj i).obj 0

def postnikovCommonRightFixedTargetRelative : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R hn f c d ≫ postnikovCommonRightZeroBase R hn f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj n) 1)
    (postnikovCommonRightZeroImageTarget R hn f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d) ≫
      postnikovCommonRightStandardClass R hn f c d) ≫ postnikovCommonRightClassToZero R hn f c d) where
  toWitness := postnikovCommonRightZeroImageTargetWitness R hn f c d
  projection_eq := (Path.Witness.hom_eq_constant R
    ((postnikovCommonRightZeroImageTargetWitness R hn f c d).postcomp
      (SquareZero.projection _ _))).trans
    (congrArg (fun t => t ≫ Path.diagonal R (postnikov R (B.obj i).obj 0))
      (postnikovCommonRightZeroImageTarget_projection R hn f c d))

def postnikovCommonRightFixedSourceRelative : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R hn f c d ≫ postnikovCommonRightZeroBase R hn f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj n) 1)
    (postnikovCommonRightZeroImageSource R hn f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d) ≫
      postnikovCommonRightDenStandardClass R hn f c d) ≫ postnikovCommonRightClassToZero R hn f c d) where
  toWitness := postnikovCommonRightZeroImageSourceWitness R hn f c d
  projection_eq := (Path.Witness.hom_eq_constant R
    ((postnikovCommonRightZeroImageSourceWitness R hn f c d).postcomp
      (SquareZero.projection _ _))).trans
    (congrArg (fun t => t ≫ Path.diagonal R (postnikov R (B.obj i).obj 0))
      (postnikovCommonRightZeroImageSource_projection R hn f c d))

def postnikovCommonRightFixedCentralRelative : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R hn f c d ≫ postnikovCommonRightZeroBase R hn f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj n) 1)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d) ≫
      postnikovCommonRightStandardClass R hn f c d) ≫ postnikovCommonRightClassToZero R hn f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d) ≫
      postnikovCommonRightDenStandardClass R hn f c d) ≫ postnikovCommonRightClassToZero R hn f c d) where
  hom := (postnikovCommonRightFixedZeroPathWitness R hn f c d).hom
  source_eq := (postnikovCommonRightFixedZeroPathWitness R hn f c d).source_eq.trans
    (postnikovCommonRightZeroPathLeft_eq R hn f c d)
  target_eq := (postnikovCommonRightFixedZeroPathWitness R hn f c d).target_eq.trans
    (postnikovCommonRightZeroPathRight_eq R hn f c d)
  projection_eq := postnikovCommonRightFixedZeroPathWitness_projection R hn f c d

def postnikovCommonRightAffineFixedGlue : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R hn f c d ≫ postnikovCommonRightZeroBase R hn f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj n) 1)
    (postnikovCommonRightZeroImageTarget R hn f c d) (postnikovCommonRightZeroImageSource R hn f c d) :=
  ((postnikovCommonRightFixedTargetRelative R hn f c d).comp
    (postnikovCommonRightFixedCentralRelative R hn f c d)).comp
    (postnikovCommonRightFixedSourceRelative R hn f c d).reverse

lemma postnikovCommonRightAffineFixedGlue_linear :
    (postnikovCommonRightAffineFixedGlue R hn f c d).hom.hom =
    (postnikovCommonRightFixedTargetRelative R hn f c d).hom.hom -
      (((cellPathNonpositiveToCell R (postnikovCommonClassBase R hn f c d) ≫
        postnikovCommonRightStandardClass R hn f c d) ≫ postnikovCommonRightClassToZero R hn f c d) ≫
          Path.diagonal R (SquareZero.algebra (postnikov R (B.obj i).obj 0)
            (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj n) 1))).hom +
      (postnikovCommonRightFixedCentralRelative R hn f c d).hom.hom +
      (postnikovCommonRightZeroImageSource R hn f c d ≫
        Path.diagonal R (SquareZero.algebra (postnikov R (B.obj i).obj 0)
            (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj n) 1))).hom -
      (postnikovCommonRightFixedSourceRelative R hn f c d).hom.hom := by
  change (((postnikovCommonRightFixedTargetRelative R hn f c d).comp _).comp _).hom.hom = _
  rw [SquareZero.RelativeWitness.comp_hom_linear, SquareZero.RelativeWitness.comp_hom_linear,
    SquareZero.RelativeWitness.reverse_hom_linear]
  abel

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
