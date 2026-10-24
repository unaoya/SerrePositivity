module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRelativeClassPath
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeExtension

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorRelativeModels

/-!
概要：二切断候補の三つの class 模型を、元の共通底上の相対模型へ準同型比較する。
方針：元の classProjection の次数全射性を、そのまま絶対模型への比較へ渡す。
規約：追加の経路や準同型の仮定を入力しない。使われ方：実逆三角形の相対経路計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma sourceClass_projection : d.sourceClass R ≫
    SquareZero.projection (d.classBase R) (d.denominatorLayer R) = d.classProjection R :=
  PostnikovSuccessorClassInverseData.sourceClass_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def sourceRelativeModel : Mon (Complex R) :=
  PostnikovSuccessorClassInverseData.sourceRelativeModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def imageRelativeModel : Mon (Complex R) :=
  PostnikovSuccessorClassInverseData.imageRelativeModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def targetRelativeModel : Mon (Complex R) :=
  PostnikovSuccessorClassInverseData.targetRelativeModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def sourceRelativeComparison : d.sourceRelativeModel R ⟶ d.sourceModel R :=
  PostnikovSuccessorClassInverseData.sourceRelativeComparison
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def imageRelativeComparison : d.imageRelativeModel R ⟶ d.imageModel R :=
  PostnikovSuccessorClassInverseData.imageRelativeComparison
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def targetRelativeComparison : d.targetRelativeModel R ⟶ d.targetModel R :=
  PostnikovSuccessorClassInverseData.targetRelativeComparison
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceRelativeComparison_quasiIso : QuasiIso (d.sourceRelativeComparison R).hom :=
  PostnikovSuccessorClassInverseData.sourceRelativeComparison_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma imageRelativeComparison_quasiIso : QuasiIso (d.imageRelativeComparison R).hom :=
  PostnikovSuccessorClassInverseData.imageRelativeComparison_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma targetRelativeComparison_quasiIso : QuasiIso (d.targetRelativeComparison R).hom :=
  PostnikovSuccessorClassInverseData.targetRelativeComparison_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
