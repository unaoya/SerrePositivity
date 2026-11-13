module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreSourceBoundary
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FiniteShapes
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareDiagramEvaluation

/-!
概要：元の pullback 錐を穿孔 core へ延長し、外側の錐と実比較辺を作る。
方針：同じ native 錐の厳密な制限と頂点を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ と合成式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionCorePuncturedSourceCone_inner_val {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedSourceCone F)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanBoundary).val =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)).val := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedSourceCone_boundary_postcomp_val F _ _
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanBoundary_projection
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionCorePuncturedSourceCone_outer_val {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedOuterCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedSourceCone F)).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 1 1)).val := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedSourceCone F)
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreOuterCospanBoundary).val = _
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedSourceCone_boundary_postcomp_val F _ _
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreOuterCospanBoundary_projection
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
