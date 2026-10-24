module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroTarget
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightBasePath
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeWitness

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の指定右経路による class 比較を零底の共通標的へ送り、元の共通底へ相対化する。
方針：元の恒等係数射を後合成し、証明済みの零射影の定数式で平方零経路を持ち上げる。
規約：元の非正次数共通源と準同型射影を保持。使われ方：標準 class の間の橋渡し。
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

abbrev postnikovCommonRightZeroPathLeft :=
  PostnikovCommonCore.postnikovCommonRightZeroPathLeft
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

abbrev postnikovCommonRightZeroPathRight :=
  PostnikovCommonCore.postnikovCommonRightZeroPathRight
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightZeroPathWitness : Path.Witness R
    (postnikovCommonRightZeroPathLeft R f c d) (postnikovCommonRightZeroPathRight R f c d) :=
  PostnikovCommonCore.postnikovCommonRightZeroPathWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroPathWitness_projection :
    (postnikovCommonRightZeroPathWitness R f c d).hom ≫ Path.map R (SquareZero.projection _ _) =
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d) ≫
      Path.diagonal R (postnikov R (B.obj i).obj 0) :=
  PostnikovCommonCore.postnikovCommonRightZeroPathWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroPathLeft_projection : postnikovCommonRightZeroPathLeft R f c d ≫
    SquareZero.projection _ _ =
      postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d :=
  PostnikovCommonCore.postnikovCommonRightZeroPathLeft_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroPathRight_projection : postnikovCommonRightZeroPathRight R f c d ≫
    SquareZero.projection _ _ =
      postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d :=
  PostnikovCommonCore.postnikovCommonRightZeroPathRight_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightZeroPathSource :=
  PostnikovCommonCore.postnikovCommonRightZeroPathSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightZeroPathTarget :=
  PostnikovCommonCore.postnikovCommonRightZeroPathTarget
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightZeroRelativeWitness : Path.Witness R
    (postnikovCommonRightZeroPathSource R f c d) (postnikovCommonRightZeroPathTarget R f c d) :=
  PostnikovCommonCore.postnikovCommonRightZeroRelativeWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroRelativeWitness_projection :
    (postnikovCommonRightZeroRelativeWitness R f c d).hom ≫ Path.map R (SquareZero.projection _ _) =
      postnikovCommonRightCellProjection R f c d ≫ Path.diagonal R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonRightZeroRelativeWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
