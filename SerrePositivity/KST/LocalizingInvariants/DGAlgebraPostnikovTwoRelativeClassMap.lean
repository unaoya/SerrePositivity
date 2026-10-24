module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassTransportIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassModelMaps
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassComposition
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeCoefficientComparison

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorRelativeClassMap

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
  PostnikovSuccessorClassInverseData.sourceToImageRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def sourceToTargetRelative : d.sourceRelativeModel R ⟶ d.targetRelativeModel R :=
  PostnikovSuccessorClassInverseData.sourceToTargetRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToTargetRelative_eq : d.sourceToTargetRelative R =
    d.sourceToImageRelative R ≫ (d.classRelativeTransportIso R).hom :=
  PostnikovSuccessorClassInverseData.sourceToTargetRelative_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToImageRelative_comparison : d.sourceToImageRelative R ≫ d.imageRelativeComparison R =
    d.sourceRelativeComparison R ≫ d.sourceToImage R :=
  PostnikovSuccessorClassInverseData.sourceToImageRelative_comparison
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToTargetRelative_left : d.sourceToTargetRelative R ≫
    SquareZeroExtension.relativeLeft (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) :=
  PostnikovSuccessorClassInverseData.sourceToTargetRelative_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToTargetRelative_right : d.sourceToTargetRelative R ≫
    SquareZeroExtension.relativeRight (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeRight (d.denominatorLayer R) (d.sourceClass R) :=
  PostnikovSuccessorClassInverseData.sourceToTargetRelative_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
