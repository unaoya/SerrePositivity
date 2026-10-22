module
public import SerrePositivity.InfinityCategories.Stable.TruncatedEdgeTransport
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreSourceComparisons
public import SerrePositivity.InfinityCategories.F2.ConeRestrictionTransport
public import SerrePositivity.InfinityCategories.Core.TerminalMappingSpace

/-!
概要：実 θ と元の始点の比較辺の合成を、同じ錐の圏で照合する。
方針：正規化した制限と全三辺を保持する実二単体を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第一合成式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open SimplicialObject.Truncated
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma excisionCoreComparisonEdge_edge {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d)
    (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)))
    (he : IsLimitCone e) :
    (excisionCoreComparisonEdge F d hd e he).edge =
      ((excisionCoreComparisonConeEdge F d hd e he).map ((truncation 2).map
        (sliceOverProjection
          (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))))).edge := by
  dsimp only [excisionCoreComparisonEdge]
  apply truncatedEdge_cast_edge
  · exact (excisionCorePuncturedOuterCone_vertex _).trans
      (excisionCorePuncturedLimitCone_vertex F d hd)
  · rfl

end SerrePositivity.InfinityCategories
