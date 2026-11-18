module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedProbeHomComparison

/-!
# 同じ probe の三つの実 Kan Hom

概要：標準・正規化テンソル・共通 frame の実 Hom はすべて Kan。
方針：元の Reedy cofibrancy・全作用素の弱同値性・全複体の fibrancy を使う。
規約：単体集合モデル構造を仮定しない。
使われ方：始域の置換を戻す実 Hom 比較の合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Reedy
open _root_.SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

lemma normalizedProbeStandardHom_kanComplex (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    KanComplex (((_root_.SerrePositivity.ComplexLimits.normalizedProbeStandardHom A).obj X).obj Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  let q := cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
  exact cosimplicialHom_kanComplex _ (q.cofibrant ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X.unop))
    (q.atObject ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X.unop)).homotopicallyConstant Y

lemma normalizedProbeTensorHom_kanComplex (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    KanComplex (((_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorHom A).obj X).obj Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  exact cosimplicialHom_kanComplex _ (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame_cofibrant A X.unop)
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor_homotopicallyConstant A
      ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X.unop)) Y

lemma normalizedProbeHomMiddle_kanComplex (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    KanComplex (((_root_.SerrePositivity.ComplexLimits.normalizedProbeHomMiddle A).obj X).obj Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  exact cosimplicialHom_kanComplex _
    (FrameOverFunctor.commonObj_cofibrant (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
      (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A))
      (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A)
      (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A) X.unop)
    (FrameOverFunctor.commonObj_homotopicallyConstant (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A)
      (cosimplicialResolutionFamily (_root_.SerrePositivity.ComplexLimits.mappingCofibrantFactorization A))
      (_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorFrame A)
      (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation A) (_root_.SerrePositivity.ComplexLimits.normalizedProbeTensorAugmentation_weak A) X.unop) Y

end SerrePositivity.ComplexLimits
