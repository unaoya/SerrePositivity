module

public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedHomFrames

/-!
# 元の標準自由 probe Hom と正規化 Hom の両実弱比較

概要：同じ共通フレームへの標準射・正規化射はともに実ホモトピー同値。
方針：実 Reedy 条件・全 augmentation・全 E 代数の fibrancy を使う。
規約：元の比較射と同じ標的代数を保つ。
使われ方：標準自由単位比較の元の Hom での検出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

lemma freeNormalizedHomFromStandard_homotopyEquivalence
    (X : (Complex A)ᵒᵖ) (B : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((freeNormalizedHomFromStandard A).app X).app B) := by
  let := modelCategory A
  have := isFibrant A B
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedFrameOverFunctor_homLeft_homotopyEquivalence (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeNormalizedProbeFrame A) (freeNormalizedProbeAugmentation A)
    (freeNormalizedProbeAugmentation_weak A) X B

lemma freeNormalizedHomFromTensor_homotopyEquivalence
    (X : (Complex A)ᵒᵖ) (B : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((freeNormalizedHomFromTensor A).app X).app B) := by
  let := modelCategory A
  have := isFibrant A B
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedFrameOverFunctor_homRight_homotopyEquivalence (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeNormalizedProbeFrame A) (freeNormalizedProbeAugmentation A)
    (freeNormalizedProbeAugmentation_weak A) (freeNormalizedProbeFrame_cofibrant A)
    (fun X _ _ f => freeNormalizedProbeFrame_homotopicallyConstant A X f) X B

lemma freeNormalizedProbeHom_kanComplex (X : (Complex A)ᵒᵖ) (B : (operad A).Algebra) :
    SSet.KanComplex (((freeNormalizedProbeHom A).obj X).obj B) := by
  let := modelCategory A
  have := isFibrant A B
  exact cosimplicialHom_kanComplex _ (freeNormalizedProbeFrame_cofibrant A X.unop)
    (freeNormalizedProbeFrame_homotopicallyConstant A X.unop) B

lemma freeNormalizedHomMiddle_kanComplex (X : (Complex A)ᵒᵖ) (B : (operad A).Algebra) :
    SSet.KanComplex (((freeNormalizedHomMiddle A).obj X).obj B) := by
  let := modelCategory A
  have := isFibrant A B
  exact cosimplicialHom_kanComplex _
    (FrameOverFunctor.commonObj_cofibrant (mappingCofibrantFactorization A)
      (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
      (freeProbeFunctor A) (freeNormalizedProbeFrame A)
      (freeNormalizedProbeAugmentation A) X.unop)
    (FrameOverFunctor.commonObj_homotopicallyConstant (mappingCofibrantFactorization A)
      (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
      (freeProbeFunctor A) (freeNormalizedProbeFrame A)
      (freeNormalizedProbeAugmentation A) (freeNormalizedProbeAugmentation_weak A) X.unop) B

end SerrePositivity.EInfinity.BarrattEccles
