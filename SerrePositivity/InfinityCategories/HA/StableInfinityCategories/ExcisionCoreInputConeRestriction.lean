module
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

def excisionCoreInputConeRestriction {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCorePunctured) ≫ F) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedConeRestriction _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanBoundary
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanBoundary_diagram F)

lemma excisionCoreInputConeRestriction_cone {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCorePunctured) ≫ F)) :
    (excisionCoreInputConeRestriction F).app (Opposite.op ⦋0⦌) c =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanBoundary).cast
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanBoundary_diagram F) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.normalizedConeRestriction_cone _ _ _ _

lemma excisionCoreInputConeRestriction_source {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X) :
    (excisionCoreInputConeRestriction F).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedSourceCone F) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2) := by
  rw [excisionCoreInputConeRestriction_cone]
  exact Subtype.ext (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedSourceCone_inner_val F)

lemma excisionCoreInputConeRestriction_limit {X : SSet.{u}} [Quasicategory X]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) :
    (excisionCoreInputConeRestriction F).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedLimitCone F d hd) = d := by
  rw [excisionCoreInputConeRestriction_cone]
  exact Subtype.ext (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedLimitCone_restrict F d hd)

lemma excisionCoreInputConeRestriction_projection {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X) :
    excisionCoreInputConeRestriction F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCorePunctured) ≫ F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedConeRestriction_projection _ _ _

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
