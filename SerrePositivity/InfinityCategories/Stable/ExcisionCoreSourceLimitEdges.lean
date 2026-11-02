module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreOuterConeRestriction
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreSourceComparisons
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.ConeRestrictionTransport
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

def excisionCoreSourceToLimitConeEdge {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d) :
    Truncated.Edge (X := (truncation 2).obj
      (sliceOver (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F)))
        (excisionCorePuncturedSourceCone F) (excisionCorePuncturedLimitCone F d hd) :=
  Classical.choice ((excisionCorePuncturedLimitCone_isLimit F d hd).nonempty_edge _)

def excisionCoreSourceToLimitOuterConeEdge {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d) :
    Truncated.Edge (X := (truncation 2).obj
      (sliceOver (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))))
        (excisionCorePuncturedOuterCone (excisionCorePuncturedSourceCone F))
          (excisionCorePuncturedOuterCone (excisionCorePuncturedLimitCone F d hd)) := by
  have h := (excisionCoreSourceToLimitConeEdge F d hd).map
    ((truncation 2).map (excisionCoreOuterConeRestriction F))
  change Truncated.Edge (X := (truncation 2).obj
    (sliceOver (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))))
      ((excisionCoreOuterConeRestriction F).app (Opposite.op ⦋0⦌)
        (excisionCorePuncturedSourceCone F))
      ((excisionCoreOuterConeRestriction F).app (Opposite.op ⦋0⦌)
        (excisionCorePuncturedLimitCone F d hd)) at h
  simpa only [excisionCoreOuterConeRestriction_cone] using h

def excisionCoreSourceToOuterConeEdge {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)))
    (he : IsLimitCone e) :
    Truncated.Edge (X := (truncation 2).obj
      (sliceOver (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))))
        (excisionCorePuncturedOuterCone (excisionCorePuncturedSourceCone F)) e :=
  Classical.choice (he.nonempty_edge _)

end SerrePositivity.InfinityCategories
