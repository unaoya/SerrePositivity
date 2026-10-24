module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueContour
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightComparisonRefinement
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightCompositeZeroCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareBoundary
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquarePrecomp

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGlueContourRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の G を含む貼合せ輪郭比較を、元の Γ 源・射影上へ移す。
方針：準同型な指定細分射を全二重経路へ前合成し、同じ P 射影に移す。
規約：G,S′,R,T′,L,W の全経路を保持。使われ方：零底の二因子分解比較との照合。
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

def postnikovCommonRightGlueContourRefinedLeft :=
  PostnikovCommonCore.postnikovCommonRightGlueContourRefinedLeft
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightGlueContourRefinedRight :=
  PostnikovCommonCore.postnikovCommonRightGlueContourRefinedRight
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightGlueContourRefinedSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightGlueContourRefinedLeft R f c d hj)
    (postnikovCommonRightGlueContourRefinedRight R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightGlueContourRefinedSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightGlueContourRefinedSquare_hom :
    (postnikovCommonRightGlueContourRefinedSquare R f c d hj).hom =
      postnikovCommonRightToClassifying R f c d ≫
        (postnikovCommonRightGlueContourSquare R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightGlueContourRefinedSquare_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightGlueContourRefinedTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightGlueContourRefinedLeft R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightGlueContourRefinedRight R f c d hj)) :=
  PostnikovCommonCore.postnikovCommonRightGlueContourRefinedTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
