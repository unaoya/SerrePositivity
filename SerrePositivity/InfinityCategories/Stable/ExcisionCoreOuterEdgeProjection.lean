module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreInputComparisonEdges
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreSourceLimitEdges
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreComparisonFirstComposite

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
namespace SerrePositivity.InfinityCategories

lemma excisionCoreOuterConeRestriction_projection {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    excisionCoreOuterConeRestriction F ≫
      sliceOverProjection (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)) =
        sliceOverProjection (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F) :=
  F2.normalizedConeRestriction_projection _ _ _

lemma excisionCoreSourceToLimitOuterConeEdge_edge {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d) :
    (excisionCoreSourceToLimitOuterConeEdge F d hd).edge =
      ((excisionCoreSourceToLimitConeEdge F d hd).map
        ((truncation 2).map (excisionCoreOuterConeRestriction F))).edge := by
  dsimp only [excisionCoreSourceToLimitOuterConeEdge]
  apply truncatedEdge_cast_edge
  · exact excisionCoreOuterConeRestriction_cone F _
  · exact excisionCoreOuterConeRestriction_cone F _

lemma excisionCoreSourceToLimitOuterConeEdge_projected_edge {X : SSet.{u}}
    [Quasicategory X] (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d) :
    ((excisionCoreSourceToLimitOuterConeEdge F d hd).map ((truncation 2).map
      (sliceOverProjection (pullbackCospan
        (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))))).edge =
      ((excisionCoreSourceToLimitConeEdge F d hd).map ((truncation 2).map
        (sliceOverProjection
          (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F)))).edge := by
  rw [Truncated.Edge.map_edge, excisionCoreSourceToLimitOuterConeEdge_edge]
  change (sliceOverProjection (pullbackCospan
    (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))).app (Opposite.op ⦋1⦌)
      ((excisionCoreOuterConeRestriction F).app (Opposite.op ⦋1⦌)
        (excisionCoreSourceToLimitConeEdge F d hd).edge) = _
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (excisionCoreOuterConeRestriction_projection F) (Opposite.op ⦋1⦌)) _

end SerrePositivity.InfinityCategories
