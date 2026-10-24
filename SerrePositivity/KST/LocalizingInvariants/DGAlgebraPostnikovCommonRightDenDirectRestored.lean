module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenAffineContour
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRightRestored

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenDirectRestored
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の直接 B 遷移の自然性と、復元した native fixed 右 class 合成を実比較する。
方針：二段分母の全射同定で両端を揃え、既存の二重経路を縦合成する。
規約：元の Γ・P・直接遷移・native 合成を保持。使われ方：実右逆三角形の模型照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightDenDirectContourPath :=
  PostnikovCommonCore.postnikovCommonRightDenDirectContourPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightDenDirectContourPath_hom :
    (postnikovCommonRightDenDirectContourPath R f c d hj).hom =
      (postnikovCommonRightDenDirectPath R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightDenDirectContourPath_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightDenDirectContourSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightDenDirectContourPath R f c d hj)
    (postnikovCommonRightDenContourPath R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightDenDirectContourSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

variable (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonRightDenDirectRestoredSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightDenDirectContourPath R f c d hj)
    (postnikovCommonClassFixedRightRestoredPath R f c d hj e) :=
  PostnikovCommonCore.postnikovCommonRightDenDirectRestoredSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonRightDenDirectRestoredTransportHomotopy :=
  PostnikovCommonCore.postnikovCommonRightDenDirectRestoredTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
