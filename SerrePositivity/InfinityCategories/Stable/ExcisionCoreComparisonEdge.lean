module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePuncturedLimitCone
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

def excisionCoreComparisonConeEdge {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d)
    (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)))
    (he : IsLimitCone e) :
    Truncated.Edge (X := (truncation 2).obj (sliceOver
      (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))))
        (excisionCorePuncturedOuterCone (excisionCorePuncturedLimitCone F d hd)) e :=
  Classical.choice (he.nonempty_edge
    (excisionCorePuncturedOuterCone (excisionCorePuncturedLimitCone F d hd)))

def excisionCoreComparisonEdge {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d)
    (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)))
    (he : IsLimitCone e) :
    Truncated.Edge (X := (truncation 2).obj X) d.vertex e.vertex := by
  have h := (excisionCoreComparisonConeEdge F d hd e he).map
    ((truncation 2).map (sliceOverProjection
      (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))))
  change Truncated.Edge (X := (truncation 2).obj X)
    (excisionCorePuncturedOuterCone (excisionCorePuncturedLimitCone F d hd)).vertex
      e.vertex at h
  simpa only [excisionCorePuncturedOuterCone_vertex,
    excisionCorePuncturedLimitCone_vertex] using h

end SerrePositivity.InfinityCategories
