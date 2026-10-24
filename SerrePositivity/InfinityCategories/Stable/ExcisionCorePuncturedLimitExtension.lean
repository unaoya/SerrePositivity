module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanDiagram
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.Stable.FiniteShapes
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

lemma excisionCorePunctured_limitCone_extension {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d) :
    ∃ c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F),
      IsLimitCone c ∧ (restrictJoinCone c excisionCoreCospanBoundary).val = d.val ∧
        c.vertex = d.vertex := by
  let := excisionCoreCospanBoundary_mono.{u}
  have := sliceOverRestrict_trivialKanFibration
    (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F)
    excisionCoreCospanBoundary excisionCoreCospanBoundary_leftAnodyne
  obtain ⟨c, hc, he, hv⟩ := exists_limitCone_extension_of_trivialRestriction _ _
    (d.cast (excisionCoreCospanBoundary_diagram F).symm)
    (hd.cast (excisionCoreCospanBoundary_diagram F).symm)
  exact ⟨c, hc, congrArg Subtype.val he, hv⟩

end SerrePositivity.InfinityCategories
