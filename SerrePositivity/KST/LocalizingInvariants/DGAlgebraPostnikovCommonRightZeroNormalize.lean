module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroDiagram
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathSourceMap

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroNormalize
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：共通零標的で三つの元の class 経路を、同じ非正次数共通源上の両端へ正規化する。
方針：元の標準 class の底変更式と一重・二重 cell 源への比較射を使用する。
規約：元の class と恒等係数の零標的射を保持。使われ方：三経路の貼り合わせ。
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

lemma postnikovCommonRightZeroPathLeft_eq : postnikovCommonRightZeroPathLeft R f c d =
    (cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d :=
  PostnikovCommonCore.postnikovCommonRightZeroPathLeft_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroPathRight_eq : postnikovCommonRightZeroPathRight R f c d =
    (cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightDenStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d :=
  PostnikovCommonCore.postnikovCommonRightZeroPathRight_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

abbrev postnikovCommonRightZeroImageSource :=
  PostnikovCommonCore.postnikovCommonRightZeroImageSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

abbrev postnikovCommonRightZeroImageTarget :=
  PostnikovCommonCore.postnikovCommonRightZeroImageTarget
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightZeroImageSourceWitness : Path.Witness R
    (postnikovCommonRightZeroImageSource R f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightDenStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d) :=
  PostnikovCommonCore.postnikovCommonRightZeroImageSourceWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightZeroImageTargetWitness : Path.Witness R
    (postnikovCommonRightZeroImageTarget R f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d) :=
  PostnikovCommonCore.postnikovCommonRightZeroImageTargetWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightZeroStandardWitness : Path.Witness R
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d)
    ((cellPathNonpositiveToCell R (postnikovCommonClassBase R f c d) ≫
      postnikovCommonRightDenStandardClass R f c d) ≫ postnikovCommonRightClassToZero R f c d) :=
  PostnikovCommonCore.postnikovCommonRightZeroStandardWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroImageTarget_projection : postnikovCommonRightZeroImageTarget R f c d ≫
    SquareZero.projection _ _ =
      postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d :=
  PostnikovCommonCore.postnikovCommonRightZeroImageTarget_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroImageSource_projection : postnikovCommonRightZeroImageSource R f c d ≫
    SquareZero.projection _ _ =
      postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d :=
  PostnikovCommonCore.postnikovCommonRightZeroImageSource_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
