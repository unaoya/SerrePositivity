module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightContourSourceRight
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueViaBComparison
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroTransportCompositeHomotopy

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGlueNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の G と分子・分母の二自然性合成を、指定 W を保つ実二重経路で結ぶ。
方針：元の左境界 S′R の全射同定を、既存の貼合せ比較へ代入する。
規約：元の Γ 源・射影・両端・G・W を保持。使われ方：実 roof の右三角形への接続。
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

def postnikovCommonRightGlueRefinedPath :=
  PostnikovCommonCore.postnikovCommonRightGlueRefinedPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightDenContourPath :=
  PostnikovCommonCore.postnikovCommonRightDenContourPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightGlueThenDen :=
  PostnikovCommonCore.postnikovCommonRightGlueThenDen
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightGlueThenDen_hom :
    (postnikovCommonRightGlueContourRefinedLeft R f c d hj).hom =
      (postnikovCommonRightGlueThenDen R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightGlueThenDen_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

/-- 元の G⋅分母自然性と分子自然性⋅W を同じ Γ 射影上で結ぶ実二重経路。 -/
def postnikovCommonRightGlueNaturalitySquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightGlueThenDen R f c d hj)
    (postnikovCommonRightViaBThenBottom R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightGlueNaturalitySquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightGlueNaturalityTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightGlueThenDen R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightViaBThenBottom R f c d hj)) :=
  PostnikovCommonCore.postnikovCommonRightGlueNaturalityTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

/-- 同じ四つの実模型射の合成を結ぶ経路。class 経路の輸送だけに留めない。 -/
def postnikovCommonRightGlueNaturalityCompositeHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightGlueRefinedPath R f c d hj) ≫
    SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightDenContourPath R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightViaBContourPath R f c d hj) ≫
    SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightContourBottomRefinedPath R f c d hj)) :=
  PostnikovCommonCore.postnikovCommonRightGlueNaturalityCompositeHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
