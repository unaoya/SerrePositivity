module
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

def excisionCoreInputConeRestriction {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    sliceOver (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F) ⟶
      sliceOver (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)) :=
  F2.normalizedConeRestriction _ excisionCoreCospanBoundary
    (excisionCoreCospanBoundary_diagram F)

lemma excisionCoreInputConeRestriction_cone {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F)) :
    (excisionCoreInputConeRestriction F).app (Opposite.op ⦋0⦌) c =
      (restrictJoinCone c excisionCoreCospanBoundary).cast
        (excisionCoreCospanBoundary_diagram F) :=
  normalizedConeRestriction_cone _ _ _ _

lemma excisionCoreInputConeRestriction_source {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    (excisionCoreInputConeRestriction F).app (Opposite.op ⦋0⦌)
      (excisionCorePuncturedSourceCone F) =
        pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 2 2) := by
  rw [excisionCoreInputConeRestriction_cone]
  exact Subtype.ext (excisionCorePuncturedSourceCone_inner_val F)

lemma excisionCoreInputConeRestriction_limit {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d) :
    (excisionCoreInputConeRestriction F).app (Opposite.op ⦋0⦌)
      (excisionCorePuncturedLimitCone F d hd) = d := by
  rw [excisionCoreInputConeRestriction_cone]
  exact Subtype.ext (excisionCorePuncturedLimitCone_restrict F d hd)

lemma excisionCoreInputConeRestriction_projection {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    excisionCoreInputConeRestriction F ≫
      sliceOverProjection (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)) =
        sliceOverProjection (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F) :=
  F2.normalizedConeRestriction_projection _ _ _

end SerrePositivity.InfinityCategories
