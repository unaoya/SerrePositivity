module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedProbeHomComparison

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

lemma normalizedProbeStandardHom_kanComplex (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    KanComplex (((normalizedProbeStandardHom A).obj X).obj Y) := by
  let := projectiveModelCategory A
  have := BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  exact cosimplicialHom_kanComplex _ (q.cofibrant ((framedLimitProbeFunctor A).obj X.unop))
    (q.atObject ((framedLimitProbeFunctor A).obj X.unop)).homotopicallyConstant Y

lemma normalizedProbeTensorHom_kanComplex (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    KanComplex (((normalizedProbeTensorHom A).obj X).obj Y) := by
  let := projectiveModelCategory A
  have := BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  exact cosimplicialHom_kanComplex _ (normalizedProbeTensorFrame_cofibrant A X.unop)
    (normalizedSimplexTensor_homotopicallyConstant A
      ((framedLimitProbeFunctor A).obj X.unop)) Y

lemma normalizedProbeHomMiddle_kanComplex (X : (Complex A)ᵒᵖ) (Y : Complex A) :
    KanComplex (((normalizedProbeHomMiddle A).obj X).obj Y) := by
  let := projectiveModelCategory A
  have := BarrattEccles.CarrierDiagram.complex_isFibrant A Y
  exact cosimplicialHom_kanComplex _
    (FrameOverFunctor.commonObj_cofibrant (mappingCofibrantFactorization A)
      (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
      (framedLimitProbeFunctor A) (normalizedProbeTensorFrame A)
      (normalizedProbeTensorAugmentation A) X.unop)
    (FrameOverFunctor.commonObj_homotopicallyConstant (mappingCofibrantFactorization A)
      (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
      (framedLimitProbeFunctor A) (normalizedProbeTensorFrame A)
      (normalizedProbeTensorAugmentation A) (normalizedProbeTensorAugmentation_weak A) X.unop) Y

end SerrePositivity.EInfinity.ComplexLimits
