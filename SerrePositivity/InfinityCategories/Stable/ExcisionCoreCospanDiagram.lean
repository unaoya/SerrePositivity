module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreOuterCospan
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.Core.FiniteShapes
public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagramEvaluation

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
namespace SerrePositivity.InfinityCategories

lemma excisionCoreCospanBoundary_diagram {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    excisionCoreCospanBoundary ≫
      (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F) =
        pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2) := by
  rw [← Category.assoc, excisionCoreCospanBoundary_projection, Category.assoc]
  rfl

lemma excisionCoreOuterCospanBoundary_diagram {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    excisionCoreOuterCospanBoundary ≫
      (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F) =
        pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1) := by
  rw [← Category.assoc, excisionCoreOuterCospanBoundary_projection, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories
