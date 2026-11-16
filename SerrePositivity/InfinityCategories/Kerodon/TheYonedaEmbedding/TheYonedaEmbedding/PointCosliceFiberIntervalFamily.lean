module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.MappingParameters
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EnrichedPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EnrichedPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceCoconeFamilyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PointCosliceFamilyHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceUniversalPrism
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
/-! 同じcosliceのfiberの全interval族と普遍円柱の制限の照合。 -/

@[expose] public section
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 同じfiber族を区間模型で読む射は、同じcoslice円柱を読む全HoFun射。 -/
lemma cosliceFiber_intervalFamilyHom_arrow {K C : SSet.{u}} {x y : C _⦋0⦌}
    (f : K ⟶ vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) y) :
    Arrow.mk (intervalFamilyHom (f ≫ cosliceFiberToIntervalMappingSpace x y)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (pointCosliceFamilyHomotopy (f ≫ vertexFiberι _ y)))) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  change yonedaEquiv (curry (intervalFamilyHomotopy
    (f ≫ cosliceFiberToIntervalMappingSpace x y)).h) =
      yonedaEquiv (curry (pointCosliceFamilyHomotopy (f ≫ vertexFiberι _ y)).h)
  change yonedaEquiv (curry ((β_ K (Δ[1] : SSet.{u})).hom ≫
    intervalMappingUncurry (f ≫ cosliceFiberToIntervalMappingSpace x y))) = _
  rw [cosliceFiberToIntervalMappingSpace_uncurry]
  rfl
end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
end
