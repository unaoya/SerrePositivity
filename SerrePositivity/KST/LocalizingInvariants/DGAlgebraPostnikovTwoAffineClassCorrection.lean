module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoAffineClassPath
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassPostTransport

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorAffineClassCorrection

/-!
概要：元の Γ の模型射と直接 affine 貼合せの模型射との差を、実補正自同型で表す。
方針：実相対ループの輸送同型と class 模型射の後合成則を使う。
規約：補正は共通源の targetRelativeModel 上。τ₂Aⱼ 上の自同型とは主張しない。
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

def classAffineTargetCorrection : d.targetRelativeModel R ≅ d.targetRelativeModel R :=
  PostnikovSuccessorClassInverseData.classAffineTargetCorrection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def sourceToTargetAffineRelative : d.sourceRelativeModel R ⟶ d.targetRelativeModel R :=
  PostnikovSuccessorClassInverseData.sourceToTargetAffineRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToTargetAffineRelative_correction : d.sourceToTargetRelative R ≫
    (d.classAffineTargetCorrection R).hom = d.sourceToTargetAffineRelative R :=
  PostnikovSuccessorClassInverseData.sourceToTargetAffineRelative_correction
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToTargetAffineRelative_left : d.sourceToTargetAffineRelative R ≫
    SquareZeroExtension.relativeLeft (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) :=
  PostnikovSuccessorClassInverseData.sourceToTargetAffineRelative_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToTargetAffineRelative_right : d.sourceToTargetAffineRelative R ≫
    SquareZeroExtension.relativeRight (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeRight (d.denominatorLayer R) (d.sourceClass R) :=
  PostnikovSuccessorClassInverseData.sourceToTargetAffineRelative_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
