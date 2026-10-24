module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassGlueViaBMap
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareComposition

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassRightZeroSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：分母自然性の零底像を、G⁻¹・native 標準自然性・元の W の実合成と比較する。
方針：元の分母比較と、G⁻¹ を前置し W を後置した標準比較を縦合成する。
規約：元の Γ・G・W・両端と底射影を保持。使われ方：fixed 右模型三角形への接続。
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
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonClassDenContourZero :=
  PostnikovCommonCore.postnikovCommonClassDenContourZero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassRightZeroSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonClassDenContourZero R f c d hj)
    (postnikovCommonClassGlueStandardBottom R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassRightZeroSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassRightZeroTransportHomotopy :=
  PostnikovCommonCore.postnikovCommonClassRightZeroTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
