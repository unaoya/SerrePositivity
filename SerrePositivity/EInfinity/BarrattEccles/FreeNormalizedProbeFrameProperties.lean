module

public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedProbeFrame

/-!
# 同じ正規化 probe の自由像の実 frame 条件

概要：元の自由像 frame は実 Reedy cofibrant で、全作用素と augmentation は弱同値。
方針：証明済みの実自由 left Quillen 関手を同じ cofibrant probe frame へ適用する。
規約：標的 E 代数や元の複体の cofibrancy を入力にしない。
使われ方：正規化フレームによる元の実自由忘却 Hom 比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

lemma freeNormalizedProbeFrame_cofibrant (X : Complex A) :
    letI := modelCategory A
    reedyLeft simplex (cofibrations (operad A).Algebra)
      (initial.to ((freeNormalizedProbeFrame A).obj X)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := modelCategory A
  have := free_isLeftQuillen A
  have := (operad A).freeAlgebraAdjunction.isLeftAdjoint
  exact leftQuillen_frame_reedyCofibrant (operad A).freeAlgebraFunctor _
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame_cofibrant A X)

lemma freeNormalizedProbeFrame_homotopicallyConstant (X : Complex A)
    {n m : SimplexCategory} (f : n ⟶ m) :
    letI := modelCategory A
    weakEquivalences (operad A).Algebra (((freeNormalizedProbeFrame A).obj X).map f) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := modelCategory A
  have := free_isLeftQuillen A
  exact leftQuillen_frame_homotopicallyConstant (operad A).freeAlgebraFunctor _
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame_cofibrant A X)
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor_homotopicallyConstant A
      ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)) f

lemma freeNormalizedProbeAugmentation_weak (X : Complex A) (n : SimplexCategory) :
    letI := modelCategory A
    weakEquivalences (operad A).Algebra (((freeNormalizedProbeAugmentation A).app X).app n) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := modelCategory A
  have := free_isLeftQuillen A
  have : IsCofibrant ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) :=
    _root_.SerrePositivity.ComplexLimits.framedLimitProbe_cofibrant A X
  exact leftQuillen_frame_augmentation_weakEquivalence (operad A).freeAlgebraFunctor _
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame_cofibrant A X)
    ((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A).app X)
    (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation_weak A X) n

end SerrePositivity.EInfinity.BarrattEccles
