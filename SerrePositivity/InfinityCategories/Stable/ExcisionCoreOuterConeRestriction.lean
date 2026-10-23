module
public import SerrePositivity.InfinityCategories.Stable.NormalizedConeRestrictionVertex
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreSourceComparisons
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConeRestrictionTransport
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

def excisionCoreOuterConeRestriction {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    sliceOver (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F) ⟶
      sliceOver (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)) :=
  F2.normalizedConeRestriction _ excisionCoreOuterCospanBoundary
    (excisionCoreOuterCospanBoundary_diagram F)

lemma excisionCoreOuterConeRestriction_cone {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F)) :
    (excisionCoreOuterConeRestriction F).app (Opposite.op ⦋0⦌) c =
      excisionCorePuncturedOuterCone c :=
  normalizedConeRestriction_cone _ _ _ _

end SerrePositivity.InfinityCategories
