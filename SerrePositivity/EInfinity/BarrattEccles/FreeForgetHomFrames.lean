module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeFunctor
public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceTargetComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.QuillenLeftFrameAugmentation

/-!
# 実自由忘却随伴の Hom 比較の同じ frame

概要：元の複体 probe の自由像の標準 frame と左像 frame を同じ共通 frame へ比較する。
方針：元の関手的 Reedy 解像と元の augmentation に共通 cofibrant 置換を適用する。
規約：標的 E 代数を置換せず、元の全二変数を保持する。
使われ方：実 U の導来 Hom 比較と ∞ 随伴への接続。
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

def freeHomSourceFrame : Complex A ⥤ (SimplexCategory ⥤ Complex A) := by
  let := projectiveModelCategory A
  exact (cosimplicialResolutionFamily (carrierProbeFactorization A)).obj

def complexSourceFrameHom : (Complex A)ᵒᵖ ⥤ Complex A ⥤ SSet.{u} :=
  (freeHomSourceFrame A).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

def freeHomImageFrame : Complex A ⥤ (SimplexCategory ⥤ (operad A).Algebra) :=
  (ComplexLimits.framedLimitProbeFunctor A ⋙ freeHomSourceFrame A) ⋙
    (Functor.whiskeringRight SimplexCategory (Complex A) (operad A).Algebra).obj
      (operad A).freeAlgebraFunctor

def freeHomImageAugmentation :
    freeHomImageFrame A ⟶ freeProbeFunctor A ⋙ Functor.const SimplexCategory := by
  let := projectiveModelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.quillenLeftFrameAugmentation (operad A).freeAlgebraFunctor
    (CosimplicialFrameFamily.ofResolution
      (cosimplicialResolutionFamily (carrierProbeFactorization A)))
    (ComplexLimits.framedLimitProbeFunctor A)

def freeHomCommonFrame : Complex A ⥤ (SimplexCategory ⥤ (operad A).Algebra) := by
  let := modelCategory A
  exact FrameOverFunctor.commonObj (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeHomImageFrame A) (freeHomImageAugmentation A)

def freeHomMiddle : (Complex A)ᵒᵖ ⥤ (operad A).Algebra ⥤ SSet.{u} :=
  (freeHomCommonFrame A).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

end SerrePositivity.EInfinity.BarrattEccles
