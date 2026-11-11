module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ConeEdgeRebase
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreComparisonConeReadback
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ArrowIdentityComposition

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

lemma excisionCoreComparisonEdge_arrowMk_of_coneEdge {X : SSet.{u}} [Quasicategory X]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 1 1)))
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone e) {p : (horn 2 2 : SSet.{u}) ⟶ X} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
    (f : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) a b)
    (ha : a.val = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedOuterCone
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedLimitCone F d hd)).val)
    (hb : b.val = e.val) :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)))) =
        Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreComparisonEdge F d hd e he)) := by
  obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_coneEdge_rebase_of_val_eq f ha hb
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreComparisonEdge_homMk_of_coneEdge F d hd e he g
  dsimp only at h
  have hh := Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hg.symm
  refine hh.trans ((congrArg Arrow.mk h).trans ?_)
  have hv := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedOuterCone_vertex
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedLimitCone F d hd)).trans
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedLimitCone_vertex F d hd)
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_eqToHom_comp (𝟭 (hoFunctor.obj X))
    (congrArg (fun v ↦ (HomotopyCategory.mk v : hoFunctor.obj X)) hv)
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreComparisonEdge F d hd e he))

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
