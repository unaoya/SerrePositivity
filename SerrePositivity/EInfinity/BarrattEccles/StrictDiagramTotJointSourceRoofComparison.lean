module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceFiberRoof
public import SerrePositivity.EInfinity.FrameHom.LiftedResolutionLeftRoof

/-!
概要：元のnative fiberの反対要素圏から、同じ元のleft-roof比較を回収する。
方針：同じsource frameと元の右置換を、既存の実roof比較の係数移送へ代入する。
規約：元の制限写像と弱同値のfiber単位を記録し、native比較の同値性はまだ主張しない。
使われ方：同じfiber制限を元の固定始域のroof比較へ照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet Limits
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance jointSourceRoofComparisonModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointSourceRoofComparisonFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩





/-- 元の同じfiberの反対要素圏を、元の固定始域のleft-roof比較へ送る実射。 -/
def strictBETotJointSourceRoofComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
        (weakEquivalences (operad A).Algebra)
        (framedLimitProbe A (AsSmall.down.obj P).1.unop)
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2) :=
  FrameHom.liftedResolutionLeftRoofColimitMap
    ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
      (framedLimitProbe A (AsSmall.down.obj P).1.unop))
    ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)

/-- 同じ元のright frameと第一分解で、同じ実roof比較は弱同値。 -/
theorem strictBETotJointSourceRoofComparison_isWeakHomotopyEquivalence
    (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofComparison A P) := by
  have := rightFrameReplacement_isFibrant (rightFrameFamily A) (AsSmall.down.obj P).2
  exact FrameHom.liftedResolutionLeftRoofColimitMap_isWeakHomotopyEquivalence
    ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
      (framedLimitProbe A (AsSmall.down.obj P).1.unop))
    ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)
    (rightFrameFamily A) (mappingCofibrantFactorization A)
end SerrePositivity.EInfinity.BarrattEccles
