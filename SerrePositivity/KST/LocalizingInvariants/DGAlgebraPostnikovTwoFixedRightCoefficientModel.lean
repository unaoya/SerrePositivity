module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightCoefficients
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassPostCoefficient

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

def rightImageClass := d.targetClass R ≫
  SquareZero.coefficientMap (d.classBase R) (d.rightTargetCoefficient R)

def rightImageRelativeModel :=
  SquareZeroExtension.relativeModel (d.rightClassifyingLayer R) (d.rightImageClass R)

def targetToRightCoefficientModel : d.targetRelativeModel R ⟶ d.rightImageRelativeModel R :=
  SquareZeroExtension.coefficientModelMap (d.rightTargetCoefficient R) (d.targetClass R)
    (d.rightImageClass R) rfl

def sourceToRightCoefficientModel : d.sourceRelativeModel R ⟶ d.rightImageRelativeModel R :=
  d.sourceToTargetFixedRelative R ≫ d.targetToRightCoefficientModel R

def fixedRightCoefficientWitness := SquareZeroExtension.postCoefficientClassWitness
  (d.classCoefficient R) (d.rightTargetCoefficient R) (d.sourceClass R) (d.targetClass R)
  (d.classFixedRelativeWitness R)

lemma sourceToRightCoefficientModel_eq : d.sourceToRightCoefficientModel R =
    SquareZeroExtension.classModelMap (d.classCoefficient R ≫ d.rightTargetCoefficient R)
      (d.sourceClass R) (d.rightImageClass R) (d.fixedRightCoefficientWitness R) := by
  let h := SquareZeroExtension.classModelMap_postCoefficient (d.classCoefficient R)
    (d.rightTargetCoefficient R) (d.sourceClass R) (d.targetClass R) (d.classFixedRelativeWitness R)
  exact h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
