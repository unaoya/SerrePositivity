module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreComparisonEdgeCoordinates

/-!
概要：同じ実比較辺を元の θ と照合し、対角の可逆性から入力面の普遍性へ戻す。
方針：全錐の写像と射影辺を保つ等号輸送、錐の圏の終性、右 fibration の反映を使う。
規約：一般安定性は仮定しない。使われ方：HA 1.4.2.15 の二条件からの切除判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionCoreComparisonEdge_homMk_of_coneEdge {X : SSet.{u}} [Quasicategory X]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 1 1)))
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone e)
    (a : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 1 1))))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedOuterCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedLimitCone F d hd)) e) :
    let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 1 1))
    let hv : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedOuterCone
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedLimitCone F d hd)).vertex = d.vertex :=
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedOuterCone_vertex _).trans
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedLimitCone_vertex F d hd)
    Truncated.HomotopyCategory.homMk (a.map ((truncation 2).map q)) =
      eqToHom (congrArg (fun v ↦ (HomotopyCategory.mk v : hoFunctor.obj X)) hv) ≫
        Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreComparisonEdge F d hd e he) := by
  intro q hv
  have ha : Truncated.HomotopyCategory.homMk a =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreComparisonConeEdge F d hd e he) :=
    he.isTerminalHo.hom_ext _ _
  have h := congrArg ((Truncated.mapHomotopyCategory ((truncation 2).map q)).map) ha
  simp only [Truncated.mapHomotopyCategory_homMk] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homMk_eqToHom_comp_of_edge_eq _ _ hv
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreComparisonEdge_edge F d hd e he).symm)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
