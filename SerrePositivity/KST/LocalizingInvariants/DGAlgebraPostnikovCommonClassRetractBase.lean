module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassRetract

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassRetractBase
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：遷移後の二 class の経路を、元の共通底上へ実際に戻す。
方針：係数逆の底の左三角形で零底を元の A の遷移に同定し、底変更の経路を適用する。
規約：元の分子・遷移と各次数全射準同型の源射影を保持。使われ方：新しい class の整合。
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
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonClassRetractBase : postnikovCommonClassBase R f c d ⟶
    postnikov R (A.obj j).obj 1 :=
  PostnikovCommonCore.postnikovCommonClassRetractBase
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassRetractBase_zero : postnikovCommonRightZeroBase R f c d ≫ e.base =
    postnikovCommonClassRetractBase R f c d (hj := hj) ≫
      postnikovTransition R (A.obj j).obj 1 0 (by omega) :=
  PostnikovCommonCore.postnikovCommonClassRetractBase_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

include e in
lemma postnikovCommonClassRetractTarget_projection :
    postnikovCommonClassRetractTarget R f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonRightZeroGlueProjection R f c d ≫
        (postnikovCommonClassRetractBase R f c d (hj := hj) ≫
          postnikovTransition R (A.obj j).obj 1 0 (by omega)) :=
  PostnikovCommonCore.postnikovCommonClassRetractTarget_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

include e in
lemma postnikovCommonClassRetractSource_projection :
    postnikovCommonClassRetractSource R f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonRightZeroGlueProjection R f c d ≫
        (postnikovCommonClassRetractBase R f c d (hj := hj) ≫
          postnikovTransition R (A.obj j).obj 1 0 (by omega)) :=
  PostnikovCommonCore.postnikovCommonClassRetractSource_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassRetractLeft :=
  PostnikovCommonCore.postnikovCommonClassRetractLeft
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassRetractRight :=
  PostnikovCommonCore.postnikovCommonClassRetractRight
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassRetractRelativeWitness : Path.Witness R
    (postnikovCommonClassRetractLeft R f c d e) (postnikovCommonClassRetractRight R f c d e) :=
  PostnikovCommonCore.postnikovCommonClassRetractRelativeWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassRetractRelativeWitness_projection :
    (postnikovCommonClassRetractRelativeWitness R f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) = postnikovCommonRightZeroGlueProjection R f c d ≫
        Path.diagonal R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonClassRetractRelativeWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
