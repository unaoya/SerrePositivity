module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightFixedBasePath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroNormalize
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessPrecomp

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightAffineFixedGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

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
      postnikovCommonRightStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d) :=
  PostnikovCommonCore.postnikovCommonRightFixedTargetRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightFixedSourceRelative : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)
    (postnikovCommonRightZeroImageSource R f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightDenStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d) :=
  PostnikovCommonCore.postnikovCommonRightFixedSourceRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightFixedCentralRelative : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightDenStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d) :=
  PostnikovCommonCore.postnikovCommonRightFixedCentralRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightAffineFixedGlue : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)
    (postnikovCommonRightZeroImageTarget R f c d) (postnikovCommonRightZeroImageSource R f c d) :=
  PostnikovCommonCore.postnikovCommonRightAffineFixedGlue
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

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
      (postnikovCommonRightFixedSourceRelative R f c d).hom.hom :=
  PostnikovCommonCore.postnikovCommonRightAffineFixedGlue_linear
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
