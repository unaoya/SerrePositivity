module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassTransportIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassModelMaps
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassComposition
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeCoefficientComparison

/-!
概要：元の Γ と同じ class 経路から、二切断候補の相対 class 模型間の実射を構成する。
方針：係数射の実模型射と構成済みの class 輸送同型を合成する。
規約：元の Q・P と Γ を保持。使われ方：実候補の両逆三角形の組立。
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

def sourceToImageRelative : d.sourceRelativeModel R ⟶ d.imageRelativeModel R :=
  SquareZeroExtension.coefficientModelMap (d.classCoefficient R)
    (d.sourceClass R) (d.imageClass R) rfl

def sourceToTargetRelative : d.sourceRelativeModel R ⟶ d.targetRelativeModel R :=
  SquareZeroExtension.classModelMap (d.classCoefficient R) (d.sourceClass R) (d.targetClass R)
    (d.classRelativeWitness R)

lemma sourceToTargetRelative_eq : d.sourceToTargetRelative R =
    d.sourceToImageRelative R ≫ (d.classRelativeTransportIso R).hom := rfl

lemma sourceToImageRelative_comparison : d.sourceToImageRelative R ≫ d.imageRelativeComparison R =
    d.sourceRelativeComparison R ≫ d.sourceToImage R := by
  simpa only [sourceToImageRelative, imageRelativeComparison, sourceRelativeComparison,
    sourceToImage, SquareZeroExtension.coefficientAbsoluteMap] using
    SquareZeroExtension.coefficientModelMap_comparison
      (d.classCoefficient R) (d.sourceClass R) (d.imageClass R) rfl

lemma sourceToTargetRelative_left : d.sourceToTargetRelative R ≫
    SquareZeroExtension.relativeLeft (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) :=
  SquareZeroExtension.classModelMap_left _ _ _ _

lemma sourceToTargetRelative_right : d.sourceToTargetRelative R ≫
    SquareZeroExtension.relativeRight (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeRight (d.denominatorLayer R) (d.sourceClass R) :=
  SquareZeroExtension.classModelMap_right _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
