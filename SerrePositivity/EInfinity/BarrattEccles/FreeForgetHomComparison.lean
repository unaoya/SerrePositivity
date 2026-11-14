module

public import SerrePositivity.EInfinity.BarrattEccles.FreeForgetHomFrames
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MappingSpaces.ResolutionHomSourceRestriction

/-!
# 実自由忘却随伴の全二変数の Hom 比較射

概要：自由 probe の元の frame Hom と、元の複体から底への frame Hom の自然な span。
方針：左は元の共通 frame 射、右は同じ probe augmentation・全次数随伴・共通 frame 射。
規約：全二変数・元の標的代数と元の忘却を保持する。
使われ方：同じ U の ∞ 随伴の Hom 入力。
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

def freeHomFromLeft : (freeProbeFunctor A).op ⋙ sourceFrameHom A ⟶ freeHomMiddle A := by
  let := modelCategory A
  exact FrameOverFunctor.homLeft (mappingCofibrantFactorization A)
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
    (freeProbeFunctor A) (freeHomImageFrame A) (freeHomImageAugmentation A)

def freeHomFromRight : complexSourceFrameHom A ⋙
    (Functor.whiskeringLeft (operad A).Algebra (Complex A) SSet.{u}).obj
      (Operad.Algebra.forget (operad A)) ⟶ freeHomMiddle A := by
  let := projectiveModelCategory A
  let := modelCategory A
  let qC := cosimplicialResolutionFamily (carrierProbeFactorization A)
  let Q := ComplexLimits.framedLimitProbeFunctor A
  let ε := ComplexLimits.framedLimitProbeComparisonNatTrans A
  let e := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.adjunctionFrameHomBifunctorIso (operad A).freeAlgebraAdjunction
    (Q ⋙ qC.obj) (𝟭 (operad A).Algebra)
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.resolutionHomSourceRestriction qC Q ε (Operad.Algebra.forget (operad A)) ≫
    e.inv ≫ FrameOverFunctor.homRight (mappingCofibrantFactorization A)
      (cosimplicialResolutionFamily (mappingCofibrantFactorization A))
      (freeProbeFunctor A) (freeHomImageFrame A) (freeHomImageAugmentation A)

end SerrePositivity.EInfinity.BarrattEccles
