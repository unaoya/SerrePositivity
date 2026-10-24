module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassBaseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackPathComparison

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassModels

/-!
概要：二切断逆の class データから、元の係数を持つ三つの実拡大模型を構成する。
方針：同じ共通源上の源 class・係数像 class・標準 class と、その元の実経路を使う。
規約：二切断との準同型比較と元の逆三角形は別工程。使われ方：実逆の模型上の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

abbrev classBase :=
  PostnikovSuccessorClassInverseData.classBase
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

abbrev denominatorLayer :=
  PostnikovSuccessorClassInverseData.denominatorLayer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

abbrev numeratorLayer :=
  PostnikovSuccessorClassInverseData.numeratorLayer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def classCoefficient : d.denominatorLayer R ⟶ d.numeratorLayer R :=
  PostnikovSuccessorClassInverseData.classCoefficient
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def sourceClass : d.classSource R ⟶ SquareZero.algebra (d.classBase R) (d.denominatorLayer R) :=
  PostnikovSuccessorClassInverseData.sourceClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def targetClass : d.classSource R ⟶ SquareZero.algebra (d.classBase R) (d.numeratorLayer R) :=
  PostnikovSuccessorClassInverseData.targetClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def imageClass : d.classSource R ⟶ SquareZero.algebra (d.classBase R) (d.numeratorLayer R) :=
  PostnikovSuccessorClassInverseData.imageClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceClass_coefficient : d.imageClass R =
    postnikovCommonClassStandardGlueLeft R f d.baseInverse d.layerInverse (hj := d.target_le) :=
  PostnikovSuccessorClassInverseData.sourceClass_coefficient
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

/-- 元の class 整合経路を、そのまま cospan 比較の入力にする。 -/
def comparisonPath : Path.Witness R (d.imageClass R)
    (𝟙 (d.classSource R) ≫ d.targetClass R) :=
  PostnikovSuccessorClassInverseData.comparisonPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

abbrev sourceModel :=
  PostnikovSuccessorClassInverseData.sourceModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

abbrev imageModel :=
  PostnikovSuccessorClassInverseData.imageModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

abbrev targetModel :=
  PostnikovSuccessorClassInverseData.targetModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

abbrev pathModel :=
  PostnikovSuccessorClassInverseData.pathModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

abbrev targetComposedModel :=
  PostnikovSuccessorClassInverseData.targetComposedModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
