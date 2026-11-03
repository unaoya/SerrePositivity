module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePuncturedOuterCone
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.Core.FiniteShapes
public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagramEvaluation

/-!
概要：元の pullback 錐を穿孔 core へ延長し、外側の錐と実比較辺を作る。
方針：同じ native 錐の厳密な制限と頂点を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ と合成式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

def excisionCorePuncturedLimitCone {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d) :
    JoinCone (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F) :=
  (excisionCorePunctured_limitCone_extension F d hd).choose

lemma excisionCorePuncturedLimitCone_isLimit {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d) : IsLimitCone (excisionCorePuncturedLimitCone F d hd) :=
  (excisionCorePunctured_limitCone_extension F d hd).choose_spec.1

lemma excisionCorePuncturedLimitCone_restrict {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d) :
    (restrictJoinCone (excisionCorePuncturedLimitCone F d hd)
      excisionCoreCospanBoundary).val = d.val :=
  (excisionCorePunctured_limitCone_extension F d hd).choose_spec.2.1

lemma excisionCorePuncturedLimitCone_vertex {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d) : (excisionCorePuncturedLimitCone F d hd).vertex = d.vertex :=
  (excisionCorePunctured_limitCone_extension F d hd).choose_spec.2.2

end SerrePositivity.InfinityCategories
