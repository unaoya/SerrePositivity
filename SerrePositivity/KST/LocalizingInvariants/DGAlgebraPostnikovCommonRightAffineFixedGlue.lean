module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightFixedBasePath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroNormalize
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c)

local instance fixedGlue_zero_lower : (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj i).obj 0

def postnikovCommonRightFixedTargetRelative : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)
    (postnikovCommonRightZeroImageTarget R f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d) where
  toWitness := postnikovCommonRightZeroImageTargetWitness R f c d
  projection_eq := (Path.Witness.hom_eq_constant R
    ((postnikovCommonRightZeroImageTargetWitness R f c d).postcomp
      (SquareZero.projection _ _))).trans
    (congrArg (fun t => t ≫ Path.diagonal R (postnikov R (B.obj i).obj 0))
      (postnikovCommonRightZeroImageTarget_projection R f c d))

def postnikovCommonRightFixedSourceRelative : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)
    (postnikovCommonRightZeroImageSource R f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightDenStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d) where
  toWitness := postnikovCommonRightZeroImageSourceWitness R f c d
  projection_eq := (Path.Witness.hom_eq_constant R
    ((postnikovCommonRightZeroImageSourceWitness R f c d).postcomp
      (SquareZero.projection _ _))).trans
    (congrArg (fun t => t ≫ Path.diagonal R (postnikov R (B.obj i).obj 0))
      (postnikovCommonRightZeroImageSource_projection R f c d))

def postnikovCommonRightFixedCentralRelative : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightDenStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d) where
  hom := (postnikovCommonRightFixedZeroPathWitness R f c d).hom
  source_eq := (postnikovCommonRightFixedZeroPathWitness R f c d).source_eq.trans
    (postnikovCommonRightZeroPathLeft_eq R f c d)
  target_eq := (postnikovCommonRightFixedZeroPathWitness R f c d).target_eq.trans
    (postnikovCommonRightZeroPathRight_eq R f c d)
  projection_eq := postnikovCommonRightFixedZeroPathWitness_projection R f c d

def postnikovCommonRightAffineFixedGlue : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)
    (postnikovCommonRightZeroImageTarget R f c d) (postnikovCommonRightZeroImageSource R f c d) :=
  ((postnikovCommonRightFixedTargetRelative R f c d).comp
    (postnikovCommonRightFixedCentralRelative R f c d)).comp
    (postnikovCommonRightFixedSourceRelative R f c d).reverse

lemma postnikovCommonRightAffineFixedGlue_linear :
    (postnikovCommonRightAffineFixedGlue R f c d).hom.hom =
    (postnikovCommonRightFixedTargetRelative R f c d).hom.hom -
      (((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
        postnikovCommonRightStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d) ≫
          Path.diagonal R (SquareZero.algebra (postnikov R (B.obj i).obj 0)
            (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1))).hom +
      (postnikovCommonRightFixedCentralRelative R f c d).hom.hom +
      (postnikovCommonRightZeroImageSource R f c d ≫
        Path.diagonal R (SquareZero.algebra (postnikov R (B.obj i).obj 0)
            (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1))).hom -
      (postnikovCommonRightFixedSourceRelative R f c d).hom.hom := by
  change (((postnikovCommonRightFixedTargetRelative R f c d).comp _).comp _).hom.hom = _
  rw [SquareZero.RelativeWitness.comp_hom_linear, SquareZero.RelativeWitness.comp_hom_linear,
    SquareZero.RelativeWitness.reverse_hom_linear]
  abel

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
