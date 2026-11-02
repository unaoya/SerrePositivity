module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreComparisonEdgeCoordinates
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

lemma excisionCoreComparisonEdge_first_composite {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d)
    (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)))
    (he : IsLimitCone e) :
    let q := sliceOverProjection
      (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))
    let hv : (excisionCorePuncturedOuterCone
        (excisionCorePuncturedLimitCone F d hd)).vertex = d.vertex :=
      (excisionCorePuncturedOuterCone_vertex _).trans
        (excisionCorePuncturedLimitCone_vertex F d hd)
    Truncated.HomotopyCategory.homMk
      ((excisionCoreSourceToLimitOuterConeEdge F d hd).map ((truncation 2).map q)) ≫
        eqToHom (congrArg (fun a ↦ (HomotopyCategory.mk a : hoFunctor.obj X)) hv) ≫
          Truncated.HomotopyCategory.homMk (excisionCoreComparisonEdge F d hd e he) =
            Truncated.HomotopyCategory.homMk
              ((excisionCoreSourceToOuterConeEdge F e he).map ((truncation 2).map q)) := by
  intro q hv
  have h := excisionCoreComparisonConeEdge_projected_composite F d hd e he
  have ht := homMk_eqToHom_comp_of_edge_eq
    ((excisionCoreComparisonConeEdge F d hd e he).map ((truncation 2).map q))
    (excisionCoreComparisonEdge F d hd e he) hv
    (excisionCoreComparisonEdge_edge F d hd e he).symm
  change Truncated.HomotopyCategory.homMk
    ((excisionCoreSourceToLimitOuterConeEdge F d hd).map ((truncation 2).map q)) ≫
      Truncated.HomotopyCategory.homMk
        ((excisionCoreComparisonConeEdge F d hd e he).map ((truncation 2).map q)) = _ at h
  rw [ht] at h
  exact h

end SerrePositivity.InfinityCategories
