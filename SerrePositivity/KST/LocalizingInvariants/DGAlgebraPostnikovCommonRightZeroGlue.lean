module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroNormalize
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathOperations

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の三つの class 比較経路を共通零標的で貼り合わせ、元の共通底へ相対化する。
方針：二度の cell 経路合成と向き反転を使い、非正次数共通源と定数零射影を回収する。
規約：源の元の共通底への各次数全射準同型を保持。使われ方：class 像の整合の実経路。
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

local instance zeroGlue_target_lowerBound : (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj i).obj 0

abbrev postnikovCommonRightZeroGlueSource :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightZeroGlueProjection : postnikovCommonRightZeroGlueSource R f c d ⟶
    postnikovCommonClassBase R f c d :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueProjection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroGlueProjection_quasiIso :
    QuasiIso (postnikovCommonRightZeroGlueProjection R f c d).hom :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueProjection_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroGlueProjection_surjective (n : ℤ) :
    Function.Surjective ((postnikovCommonRightZeroGlueProjection R f c d).hom.f n) :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueProjection_surjective
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (degree := n)

def postnikovCommonRightZeroGlueWitness : Path.Witness R
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
      postnikovCommonRightZeroImageTarget R f c d)
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
      postnikovCommonRightZeroImageSource R f c d) :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroGlueLeft_projection :
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
      postnikovCommonRightZeroImageTarget R f c d) ≫ SquareZero.projection _ _ =
    postnikovCommonRightZeroGlueProjection R f c d ≫ postnikovCommonRightZeroBase R f c d :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueLeft_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroGlueRight_projection :
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
      postnikovCommonRightZeroImageSource R f c d) ≫ SquareZero.projection _ _ =
    postnikovCommonRightZeroGlueProjection R f c d ≫ postnikovCommonRightZeroBase R f c d :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueRight_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroGlueWitness_projection :
    (postnikovCommonRightZeroGlueWitness R f c d).hom ≫ Path.map R (SquareZero.projection _ _) =
    (postnikovCommonRightZeroGlueProjection R f c d ≫ postnikovCommonRightZeroBase R f c d) ≫
      Path.diagonal R (postnikov R (B.obj i).obj 0) :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightZeroGlueLeft :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueLeft
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightZeroGlueRight :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueRight
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightZeroGlueRelativeWitness : Path.Witness R
    (postnikovCommonRightZeroGlueLeft R f c d)
    (postnikovCommonRightZeroGlueRight R f c d) :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueRelativeWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroGlueRelativeWitness_projection :
    (postnikovCommonRightZeroGlueRelativeWitness R f c d).hom ≫
      Path.map R (SquareZero.projection _ _) =
    postnikovCommonRightZeroGlueProjection R f c d ≫
      Path.diagonal R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueRelativeWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
