module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareSolveLeft
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareMapOver

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGlueSolved
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の G を実二重経路で相殺し、分母自然性を G⁻¹⋅分子自然性⋅W と比較する。
方針：元の指定自然性四角形に反転を前置し、零底への二重経路も保持する。
規約：元の Γ・G・W と両端を保持。使われ方：fixed class 互換性の右三角形。
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

def postnikovCommonRightGlueSolvedPath :=
  PostnikovCommonCore.postnikovCommonRightGlueSolvedPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightGlueSolvedSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightDenContourPath R f c d hj)
    (postnikovCommonRightGlueSolvedPath R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightGlueSolvedSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightGlueSolvedZeroSquare :=
  PostnikovCommonCore.postnikovCommonRightGlueSolvedZeroSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightGlueSolvedTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightDenContourPath R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightGlueSolvedPath R f c d hj)) :=
  PostnikovCommonCore.postnikovCommonRightGlueSolvedTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
