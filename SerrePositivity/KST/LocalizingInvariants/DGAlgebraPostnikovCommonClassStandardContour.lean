module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardNaturalitySquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueSolved

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandardContour
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：native 標準像と fⱼ の自然性の合成を、元の輪郭の端点表示へ厳密に移す。
方針：ViaB の全射が元の輪郭の全射と一致することから、二重経路の端点を移す。
規約：合成と二重経路の全射を変えない。使われ方：G の反転と元の W の接続。
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

def postnikovCommonClassViaBContourZero :=
  PostnikovCommonCore.postnikovCommonClassViaBContourZero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassStandardViaB_contour_hom :
    (postnikovCommonClassStandardViaBZeroRelative R f c d hj).hom =
      (postnikovCommonClassViaBContourZero R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonClassStandardViaB_contour_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassStandardContourPath :=
  PostnikovCommonCore.postnikovCommonClassStandardContourPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassStandardContourPath_hom :
    (postnikovCommonClassStandardContourPath R f c d hj).hom =
      (postnikovCommonClassStandardThenNaturality R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonClassStandardContourPath_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassStandardContourSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonClassStandardContourPath R f c d hj)
    (postnikovCommonClassViaBContourZero R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassStandardContourSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
