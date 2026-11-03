module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreSourceBoundary
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

lemma excisionCorePuncturedSourceCone_inner_val {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    (restrictJoinCone (excisionCorePuncturedSourceCone F)
      excisionCoreCospanBoundary).val =
        (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)).val := by
  apply excisionCorePuncturedSourceCone_boundary_postcomp_val F _ _
    excisionCoreCospanBoundary_projection
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionCorePuncturedSourceCone_outer_val {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    (excisionCorePuncturedOuterCone (excisionCorePuncturedSourceCone F)).val =
      (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)).val := by
  change (restrictJoinCone (excisionCorePuncturedSourceCone F)
    excisionCoreOuterCospanBoundary).val = _
  apply excisionCorePuncturedSourceCone_boundary_postcomp_val F _ _
    excisionCoreOuterCospanBoundary_projection
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories
