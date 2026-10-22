module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePuncturedLimitExtension
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.Stable.FiniteShapes
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

def excisionCorePuncturedOuterCone {X : SSet.{u}}
    {F : nerve ExcisionGridCoreIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F)) :
    JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)) :=
  (F2.restrictJoinCone c excisionCoreOuterCospanBoundary).cast
    (excisionCoreOuterCospanBoundary_diagram F)

lemma excisionCorePuncturedOuterCone_vertex {X : SSet.{u}}
    {F : nerve ExcisionGridCoreIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F)) :
    (excisionCorePuncturedOuterCone c).vertex = c.vertex :=
  F2.restrictJoinCone_vertex c _

end SerrePositivity.InfinityCategories
