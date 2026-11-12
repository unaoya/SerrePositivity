module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EdgeHomotopyTransportSquare
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

lemma excisionCoreSourceOuter_to_input_vertex {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedOuterCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedSourceCone F)).vertex =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)).vertex := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedOuterCone_vertex]
  have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreInputConeRestriction_source F)
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreInputConeRestriction_cone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone_vertex] at h
  exact h

lemma excisionCoreComparisonEdge_input_composite {X : SSet.{u}} [Quasicategory X]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 1 1)))
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone e) :
    let qi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2))
    let qo := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 1 1))
    Truncated.HomotopyCategory.homMk
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreSourceToInputConeEdge F d hd).map ((truncation 2).map qi)) ≫
        Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreComparisonEdge F d hd e he) =
          eqToHom (congrArg (fun a ↦ (HomotopyCategory.mk a : hoFunctor.obj X))
            (excisionCoreSourceOuter_to_input_vertex F).symm) ≫
              Truncated.HomotopyCategory.homMk
                ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreSourceToOuterConeEdge F e he).map ((truncation 2).map qo)) := by
  intro qi qo
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreComparisonEdge_first_composite F d hd e he
  have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homMk_edge_square_of_edge_eq
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreSourceToLimitOuterConeEdge F d hd).map ((truncation 2).map qo))
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreSourceToInputConeEdge F d hd).map ((truncation 2).map qi))
    (excisionCoreSourceOuter_to_input_vertex F)
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedOuterCone_vertex _).trans
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedLimitCone_vertex F d hd))
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreSourceToLimitOuterConeEdge_projected_edge F d hd).trans
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreSourceToInputConeEdge_projected_edge F d hd).symm)
  dsimp only at h
  rw [← Category.assoc, ht] at h
  apply (cancel_epi (eqToHom (congrArg
    (fun a ↦ (HomotopyCategory.mk a : hoFunctor.obj X))
      (excisionCoreSourceOuter_to_input_vertex F)))).mp
  simpa only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] using h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
