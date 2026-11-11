module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreInputConeRestriction
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreSourceLimitEdges
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreComparisonFirstComposite

/-!
概要：実 θ の第一合成式を、元の内外の pullback 錐の比較辺へ同定する。
方針：正規化した入力制限と同じ頂点射影、極限錐への辺の一意性を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第一条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open SimplicialObject.Truncated
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionCoreSourceToInputConeEdge {X : SSet.{u}} [Quasicategory X]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) :
    Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)) d := by
  have h := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreSourceToLimitConeEdge F d hd).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreInputConeRestriction F))
  change Truncated.Edge (X := (truncation 2).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2))))
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreInputConeRestriction F).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedSourceCone F))
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreInputConeRestriction F).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedLimitCone F d hd)) at h
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreInputConeRestriction_source,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreInputConeRestriction_limit] using h

lemma excisionCoreSourceToInputConeEdge_hom_eq {X : SSet.{u}} [Quasicategory X]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d)
    (g : Truncated.Edge (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)) d) :
    Truncated.HomotopyCategory.homMk (excisionCoreSourceToInputConeEdge F d hd) =
      Truncated.HomotopyCategory.homMk g := hd.isTerminalHo.hom_ext _ _

lemma excisionCoreSourceToInputConeEdge_edge {X : SSet.{u}} [Quasicategory X]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) :
    (excisionCoreSourceToInputConeEdge F d hd).edge =
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreSourceToLimitConeEdge F d hd).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreInputConeRestriction F))).edge := by
  dsimp only [excisionCoreSourceToInputConeEdge]
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.truncatedEdge_cast_edge
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreInputConeRestriction_source F
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreInputConeRestriction_limit F d hd

lemma excisionCoreSourceToInputConeEdge_projected_edge {X : SSet.{u}} [Quasicategory X]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) :
    ((excisionCoreSourceToInputConeEdge F d hd).map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2))))).edge =
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreSourceToLimitConeEdge F d hd).map ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
          (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCorePunctured) ≫ F)))).edge := by
  rw [Truncated.Edge.map_edge, excisionCoreSourceToInputConeEdge_edge]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2))).app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreInputConeRestriction F).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreSourceToLimitConeEdge F d hd).edge) = _
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreInputConeRestriction_projection F) (Opposite.op ⦋1⦌)) _

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
