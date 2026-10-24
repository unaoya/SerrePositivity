module

public import
SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRightDenLiftComparison

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightRestored
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の P 上で、元の分母自然性と復元した native 右 class 合成を実比較する。
方針：分母経路の全射の同定で端点を揃え、持ち上げた全二重経路を保持する。
規約：Γ 射影と native 零 class 像も厳密に保持。使われ方：元の右模型三角形の復元。
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
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonClassFixedRightRestoredPath :=
  PostnikovCommonCore.postnikovCommonClassFixedRightRestoredPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedRightRestoredPath_hom :
    (postnikovCommonClassFixedRightRestoredPath R f c d hj e).hom =
      (postnikovCommonClassFixedRightCompletedLift R f c d hj e).hom :=
  PostnikovCommonCore.postnikovCommonClassFixedRightRestoredPath_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassFixedRightRestoredSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightDenContourPath R f c d hj)
    (postnikovCommonClassFixedRightRestoredPath R f c d hj e) :=
  PostnikovCommonCore.postnikovCommonClassFixedRightRestoredSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedRightRestoredPath_map :
    (postnikovCommonClassFixedRightRestoredPath R f c d hj e).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (postnikovCommonClassFixedRightCompletedPath R f c d hj e).hom :=
  PostnikovCommonCore.postnikovCommonClassFixedRightRestoredPath_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassFixedRightRestoredTransportHomotopy :=
  PostnikovCommonCore.postnikovCommonClassFixedRightRestoredTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
