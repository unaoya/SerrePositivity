module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightContourBottomPath
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueContourRefinement

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGlueViaBComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の G・S′R と W を保つ貼合せ比較に、既存 affineViaB を実際に代入する。
方針：T′(LW) の結合則と T′L の全射同定により、元の二重経路の右辺だけを移す。
規約：指定経路 W や左辺を定数扱いしない。使われ方：元の Γ の右逆三角形への接続。
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

lemma postnikovCommonRightGlueViaBRight_hom :
    (postnikovCommonRightGlueContourRefinedRight R f c d hj).hom =
      (postnikovCommonRightViaBThenBottom R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightGlueViaBRight_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

/-- 元の G(S′R) と affineViaB⋅W を、全底射影と両端を固定して結ぶ実二重経路。 -/
def postnikovCommonRightGlueViaBSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightGlueContourRefinedLeft R f c d hj)
    (postnikovCommonRightViaBThenBottom R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightGlueViaBSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightGlueViaBTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightGlueContourRefinedLeft R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightViaBThenBottom R f c d hj)) :=
  PostnikovCommonCore.postnikovCommonRightGlueViaBTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
