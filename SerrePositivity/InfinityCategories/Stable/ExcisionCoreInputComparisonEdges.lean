module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreInputConeRestriction
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

def excisionCoreSourceToInputConeEdge {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d) :
    Truncated.Edge (X := (truncation 2).obj
      (sliceOver (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2))))
        (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)) d := by
  have h := (excisionCoreSourceToLimitConeEdge F d hd).map
    ((truncation 2).map (excisionCoreInputConeRestriction F))
  change Truncated.Edge (X := (truncation 2).obj
    (sliceOver (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2))))
      ((excisionCoreInputConeRestriction F).app (Opposite.op ⦋0⦌)
        (excisionCorePuncturedSourceCone F))
      ((excisionCoreInputConeRestriction F).app (Opposite.op ⦋0⦌)
        (excisionCorePuncturedLimitCone F d hd)) at h
  simpa only [excisionCoreInputConeRestriction_source,
    excisionCoreInputConeRestriction_limit] using h

lemma excisionCoreSourceToInputConeEdge_hom_eq {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d)
    (g : Truncated.Edge (X := (truncation 2).obj
      (sliceOver (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2))))
        (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)) d) :
    Truncated.HomotopyCategory.homMk (excisionCoreSourceToInputConeEdge F d hd) =
      Truncated.HomotopyCategory.homMk g := hd.isTerminalHo.hom_ext _ _

lemma excisionCoreSourceToInputConeEdge_edge {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d) :
    (excisionCoreSourceToInputConeEdge F d hd).edge =
      ((excisionCoreSourceToLimitConeEdge F d hd).map
        ((truncation 2).map (excisionCoreInputConeRestriction F))).edge := by
  dsimp only [excisionCoreSourceToInputConeEdge]
  apply truncatedEdge_cast_edge
  · exact excisionCoreInputConeRestriction_source F
  · exact excisionCoreInputConeRestriction_limit F d hd

lemma excisionCoreSourceToInputConeEdge_projected_edge {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d) :
    ((excisionCoreSourceToInputConeEdge F d hd).map ((truncation 2).map
      (sliceOverProjection (pullbackCospan
        (grid22Face (excisionGridCoreDiagram ≫ F) 2 2))))).edge =
      ((excisionCoreSourceToLimitConeEdge F d hd).map ((truncation 2).map
        (sliceOverProjection
          (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F)))).edge := by
  rw [Truncated.Edge.map_edge, excisionCoreSourceToInputConeEdge_edge]
  change (sliceOverProjection (pullbackCospan
    (grid22Face (excisionGridCoreDiagram ≫ F) 2 2))).app (Opposite.op ⦋1⦌)
      ((excisionCoreInputConeRestriction F).app (Opposite.op ⦋1⦌)
        (excisionCoreSourceToLimitConeEdge F d hd).edge) = _
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (excisionCoreInputConeRestriction_projection F) (Opposite.op ⦋1⦌)) _

end SerrePositivity.InfinityCategories
