module

public import SerrePositivity.EInfinity.BarrattEccles.FreeForgetHomComparison

/-!
# 実自由忘却 Hom span の三つの Kan 性

概要：同じ自由 probe 側・共通側・元の底への Hom はすべて Kan。
方針：元の frame の cofibrancy と全対象の fibrancy を使う。
規約：単体集合のモデル構造を仮定しない。
使われ方：導来 Hom span の実ホモトピー同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A]

lemma freeHomLeft_kanComplex (X : (Complex A)ᵒᵖ) (B : (operad A).Algebra) :
    SSet.KanComplex ((((freeProbeFunctor A).op ⋙ sourceFrameHom A).obj X).obj B) :=
  sourceFrameHom_kanComplex A _ B

lemma freeHomRight_kanComplex (X : (Complex A)ᵒᵖ) (B : (operad A).Algebra) :
    SSet.KanComplex (((complexSourceFrameHom A).obj X).obj B.carrier) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  letI : CategoryTheory.Limits.HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩
  let := modelCategory A
  have := forget_isRightQuillen A
  have := (operad A).freeAlgebraAdjunction.isRightAdjoint
  have := isFibrant A B
  have : IsFibrant B.carrier := SerrePositivity.Quillen.isFibrant_obj
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)) B
  let qC := cosimplicialResolutionFamily (carrierProbeFactorization A)
  exact cosimplicialHom_kanComplex _ (qC.cofibrant X.unop)
    (qC.atObject X.unop).homotopicallyConstant B.carrier

lemma freeHomMiddle_kanComplex (X : (Complex A)ᵒᵖ) (B : (operad A).Algebra) :
    SSet.KanComplex (((freeHomMiddle A).obj X).obj B) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := modelCategory A
  have := free_isLeftQuillen A
  have := isFibrant A B
  let qC := cosimplicialResolutionFamily (carrierProbeFactorization A)
  let P := CosimplicialFrameFamily.ofResolution qC
  let Q := _root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A
  let qD := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  have ha : ∀ X n, weakEquivalences (operad A).Algebra
      (((freeHomImageAugmentation A).app X).app n) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenLeftFrameAugmentation_weak (operad A).freeAlgebraFunctor P Q
      (_root_.SerrePositivity.ComplexLimits.framedLimitProbe_cofibrant A)
  exact cosimplicialHom_kanComplex _
    (FrameOverFunctor.commonObj_cofibrant (mappingCofibrantFactorization A) qD
      (freeProbeFunctor A) (freeHomImageFrame A) (freeHomImageAugmentation A) X.unop)
    (FrameOverFunctor.commonObj_homotopicallyConstant (mappingCofibrantFactorization A) qD
      (freeProbeFunctor A) (freeHomImageFrame A) (freeHomImageAugmentation A) ha X.unop) B

end SerrePositivity.EInfinity.BarrattEccles
