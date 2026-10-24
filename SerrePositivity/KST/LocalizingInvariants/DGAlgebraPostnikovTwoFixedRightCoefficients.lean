module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedClassMap
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassRightCoefficientZeroMap

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightCoefficients

/-!
概要：元の二切断 fixed roof の係数射を、元の fⱼ と直接 B 遷移の同じ値域へ固定する。
方針：構成済みの実双加群射と厳密な右三角形を、元の class 逆データへ適用する。
規約：fixed roof が実際に使う classCoefficient を保持。使われ方：右模型合成の照合。
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

abbrev rightClassifyingLayer :=
  PostnikovSuccessorClassInverseData.rightClassifyingLayer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightTargetCoefficient : d.numeratorLayer R ⟶ d.rightClassifyingLayer R :=
  PostnikovSuccessorClassInverseData.rightTargetCoefficient
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rightDenominatorCoefficient : d.denominatorLayer R ⟶ d.rightClassifyingLayer R :=
  PostnikovSuccessorClassInverseData.rightDenominatorCoefficient
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma classCoefficient_right_triangle :
    d.classCoefficient R ≫ d.rightTargetCoefficient R = d.rightDenominatorCoefficient R :=
  PostnikovSuccessorClassInverseData.classCoefficient_right_triangle
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma classCoefficient_right_triangle_map :
    SquareZero.coefficientMap (d.classBase R) (d.classCoefficient R) ≫
      SquareZero.coefficientMap (d.classBase R) (d.rightTargetCoefficient R) =
    SquareZero.coefficientMap (d.classBase R) (d.rightDenominatorCoefficient R) :=
  PostnikovSuccessorClassInverseData.classCoefficient_right_triangle_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightTargetCoefficient_zero_map :
    SquareZero.coefficientMap (d.classBase R) (d.rightTargetCoefficient R) ≫
      SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1) =
    postnikovCommonClassFixedZeroMap R f d.baseInverse d.layerInverse d.target_le :=
  PostnikovSuccessorClassInverseData.rightTargetCoefficient_zero_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
