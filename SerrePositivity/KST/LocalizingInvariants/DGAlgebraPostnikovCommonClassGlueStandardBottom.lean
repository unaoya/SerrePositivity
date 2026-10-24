module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardContour
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareAppend
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquarePrepend

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassGlueStandardBottom
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：native 標準像の実比較に、元の G の反転と指定 W を接続する。
方針：同じ端点表示の二重経路へ W を後置し、G の反転を前置する。
規約：元の Γ・G・W と全二重経路を保持。使われ方：分母側との右 class 比較。
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

def postnikovCommonClassContourBottomZero :=
  PostnikovCommonCore.postnikovCommonClassContourBottomZero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassStandardThenBottom :=
  PostnikovCommonCore.postnikovCommonClassStandardThenBottom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassViaBThenBottomZero :=
  PostnikovCommonCore.postnikovCommonClassViaBThenBottomZero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassGlueStandardBottom :=
  PostnikovCommonCore.postnikovCommonClassGlueStandardBottom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassGlueViaBBottom :=
  PostnikovCommonCore.postnikovCommonClassGlueViaBBottom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassGlueStandardBottomSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonClassGlueStandardBottom R f c d hj)
    (postnikovCommonClassGlueViaBBottom R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassGlueStandardBottomSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
