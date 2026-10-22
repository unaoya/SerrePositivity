module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRelativeClassPath
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeExtension

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
    SquareZero.projection (d.classBase R) (d.denominatorLayer R) = d.classProjection R := by
  rw [sourceClass, Category.assoc]
  erw [postnikovCellClassOver_projection, postnikovCommonClassCompatibilityToCell_projection]
  rfl

def sourceRelativeModel : Mon (Complex R) :=
  SquareZeroExtension.relativeModel (d.denominatorLayer R) (d.sourceClass R)

def imageRelativeModel : Mon (Complex R) :=
  SquareZeroExtension.relativeModel (d.numeratorLayer R) (d.imageClass R)

def targetRelativeModel : Mon (Complex R) :=
  SquareZeroExtension.relativeModel (d.numeratorLayer R) (d.targetClass R)

def sourceRelativeComparison : d.sourceRelativeModel R ⟶ d.sourceModel R :=
  SquareZeroExtension.relativeComparison (d.denominatorLayer R) (d.sourceClass R)

def imageRelativeComparison : d.imageRelativeModel R ⟶ d.imageModel R :=
  SquareZeroExtension.relativeComparison (d.numeratorLayer R) (d.imageClass R)

def targetRelativeComparison : d.targetRelativeModel R ⟶ d.targetModel R :=
  SquareZeroExtension.relativeComparison (d.numeratorLayer R) (d.targetClass R)

lemma sourceRelativeComparison_quasiIso : QuasiIso (d.sourceRelativeComparison R).hom := by
  apply SquareZeroExtension.relativeComparison_quasiIso
  rw [d.sourceClass_projection R]
  exact d.classProjection_surjective R

lemma imageRelativeComparison_quasiIso : QuasiIso (d.imageRelativeComparison R).hom := by
  apply SquareZeroExtension.relativeComparison_quasiIso
  rw [(d.classRelativeWitness R).source_projection]
  exact d.classProjection_surjective R

lemma targetRelativeComparison_quasiIso : QuasiIso (d.targetRelativeComparison R).hom := by
  apply SquareZeroExtension.relativeComparison_quasiIso
  rw [(d.classRelativeWitness R).target_projection]
  exact d.classProjection_surjective R

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
