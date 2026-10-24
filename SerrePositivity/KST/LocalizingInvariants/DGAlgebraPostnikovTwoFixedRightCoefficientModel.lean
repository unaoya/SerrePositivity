module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightCoefficients
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassPostCoefficient

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightCoefficientModel

/-!
概要：fixed roof の元の実模型射へ fⱼ の係数模型射を後合成した実射を表示する。
方針：元の sourceToTargetFixedRelative に、class 模型射の厳密な係数後合成則を適用する。
規約：元の模型射と係数を保持。使われ方：native 右 class 合成との実模型照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def rightImageClass :=
  PostnikovSuccessorClassInverseData.rightImageClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightImageRelativeModel :=
  PostnikovSuccessorClassInverseData.rightImageRelativeModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def targetToRightCoefficientModel : d.targetRelativeModel R ⟶ d.rightImageRelativeModel R :=
  PostnikovSuccessorClassInverseData.targetToRightCoefficientModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def sourceToRightCoefficientModel : d.sourceRelativeModel R ⟶ d.rightImageRelativeModel R :=
  PostnikovSuccessorClassInverseData.sourceToRightCoefficientModel
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedRightCoefficientWitness :=
  PostnikovSuccessorClassInverseData.fixedRightCoefficientWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToRightCoefficientModel_eq : d.sourceToRightCoefficientModel R =
    SquareZeroExtension.classModelMap (d.classCoefficient R ≫ d.rightTargetCoefficient R)
      (d.sourceClass R) (d.rightImageClass R) (d.fixedRightCoefficientWitness R) :=
  PostnikovSuccessorClassInverseData.sourceToRightCoefficientModel_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
