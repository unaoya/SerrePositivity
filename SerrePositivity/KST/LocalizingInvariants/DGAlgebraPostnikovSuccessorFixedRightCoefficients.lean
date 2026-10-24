module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedClassMap
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassRightCoefficientZeroMap

/-!
概要：元の次段切断 fixed roof の係数射を、元の fⱼ と直接 B 遷移の同じ値域へ固定する。
方針：構成済みの実双加群射と厳密な右三角形を、元の class 逆データへ適用する。
規約：fixed roof が実際に使う classCoefficient を保持。使われ方：右模型合成の照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

abbrev rightClassifyingLayer :=
  PostnikovCommonCore.postnikovCommonRightClassifyingLayer R hn f d.baseInverse d.layerInverse d.target_le

def rightTargetCoefficient : d.numeratorLayer R ⟶ d.rightClassifyingLayer R :=
  PostnikovCommonCore.postnikovCommonClassRightTargetCoefficient R hn f d.baseInverse d.layerInverse d.target_le

def rightDenominatorCoefficient : d.denominatorLayer R ⟶ d.rightClassifyingLayer R :=
  PostnikovCommonCore.postnikovCommonClassRightDenominatorCoefficient R hn f d.baseInverse d.layerInverse d.target_le

lemma classCoefficient_right_triangle :
    d.classCoefficient R ≫ d.rightTargetCoefficient R = d.rightDenominatorCoefficient R := by
  let h := PostnikovCommonCore.postnikovCommonClassRightCoefficient_triangle R hn f
    d.baseInverse d.layerInverse d.target_le
  exact h

lemma classCoefficient_right_triangle_map :
    SquareZero.coefficientMap (d.classBase R) (d.classCoefficient R) ≫
      SquareZero.coefficientMap (d.classBase R) (d.rightTargetCoefficient R) =
    SquareZero.coefficientMap (d.classBase R) (d.rightDenominatorCoefficient R) := by
  let h := SquareZero.coefficientMap_comp (d.classCoefficient R) (d.rightTargetCoefficient R)
  exact h.trans
    (congrArg (SquareZero.coefficientMap (d.classBase R)) (d.classCoefficient_right_triangle R))

lemma rightTargetCoefficient_zero_map :
    SquareZero.coefficientMap (d.classBase R) (d.rightTargetCoefficient R) ≫
      SquareZero.baseChangeMap
        (PostnikovCommonCore.postnikovCommonRightClassifyingBase R hn f d.baseInverse d.layerInverse d.target_le)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1) =
    PostnikovCommonCore.postnikovCommonClassFixedZeroMap R hn f d.baseInverse d.layerInverse d.target_le := by
  let h := PostnikovCommonCore.postnikovCommonClassRightTargetCoefficient_zero_map R hn f
    d.baseInverse d.layerInverse d.target_le
  exact h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
