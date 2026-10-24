module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightAffineFixedGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassGlue

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightFixedClassGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：指定右経路の affine 貼合せを、元の共通源と native class 標的へ戻す。
方針：既存の源射影で前合成し、同じ底変更同型の逆を使う。
規約：元の二つの右 class 像と同じ両端を保持。使われ方：整合する Γ class 互換性。
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
  (d : PostnikovCommonLayerInverse R f c)

def postnikovCommonRightFixedZeroGlueWitness : Path.Witness R
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
      postnikovCommonRightZeroImageTarget R f c d)
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
      postnikovCommonRightZeroImageSource R f c d) :=
  PostnikovCommonCore.postnikovCommonRightFixedZeroGlueWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightFixedZeroGlueWitness_projection :
    (postnikovCommonRightFixedZeroGlueWitness R f c d).hom ≫
      Path.map R (SquareZero.projection _ _) =
    (postnikovCommonRightZeroGlueProjection R f c d ≫ postnikovCommonRightZeroBase R f c d) ≫
      Path.diagonal R (postnikov R (B.obj i).obj 0) :=
  PostnikovCommonCore.postnikovCommonRightFixedZeroGlueWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightFixedZeroGlueRelativeWitness : Path.Witness R
    (postnikovCommonRightZeroGlueLeft R f c d) (postnikovCommonRightZeroGlueRight R f c d) :=
  PostnikovCommonCore.postnikovCommonRightFixedZeroGlueRelativeWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightFixedZeroGlueRelativeWitness_projection :
    (postnikovCommonRightFixedZeroGlueRelativeWitness R f c d).hom ≫
      Path.map R (SquareZero.projection _ _) =
    postnikovCommonRightZeroGlueProjection R f c d ≫
      Path.diagonal R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonRightFixedZeroGlueRelativeWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightFixedClassGlueWitness : Path.Witness R
    (postnikovCommonRightGlueTarget R f c d) (postnikovCommonRightGlueSource R f c d) :=
  PostnikovCommonCore.postnikovCommonRightFixedClassGlueWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightFixedClassGlueWitness_projection :
    (postnikovCommonRightFixedClassGlueWitness R f c d).hom ≫
      Path.map R (SquareZero.projection _ _) = postnikovCommonRightZeroGlueProjection R f c d ≫
        Path.diagonal R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonRightFixedClassGlueWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightFixedClassGlueRelative : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R f c d)
    (DGBimoduleShift.obj (postnikovCommonRightLayer R f c d) 1)
    (postnikovCommonRightGlueTarget R f c d) (postnikovCommonRightGlueSource R f c d) :=
  PostnikovCommonCore.postnikovCommonRightFixedClassGlueRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
