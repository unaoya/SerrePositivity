module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardComposite
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareMapOver
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareReindex
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeEndpointTransfer

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandardNaturalitySquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の標準経路像と fⱼ の自然性の合成を、ViaB と実二重経路で比較する。
方針：元の ViaA→ViaB の二重経路を零 class 標的へ写し、全射同定で表示を移す。
規約：元の Γ 射影・両端と全二重経路を保持。使われ方：fixed 右 class 三角形。
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

def postnikovCommonClassStandardViaAZeroRelative :=
  PostnikovCommonCore.postnikovCommonClassStandardViaAZeroRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassStandardViaBRawZeroRelative :=
  PostnikovCommonCore.postnikovCommonClassStandardViaBRawZeroRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassStandardViaBZeroRelative :=
  PostnikovCommonCore.postnikovCommonClassStandardViaBZeroRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassStandardNaturalitySquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonClassStandardThenNaturality R f c d hj)
    (postnikovCommonClassStandardViaBZeroRelative R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassStandardNaturalitySquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassStandardNaturalityTransportHomotopy :=
  PostnikovCommonCore.postnikovCommonClassStandardNaturalityTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
