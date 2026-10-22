module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreComparisonEdge
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

def excisionGridCoreSourceInitial : IsInitial (excisionGridCorePoint.{u} 0 0) :=
  IsInitial.ofUniqueHom (fun _ ↦ homOfLE ⟨Nat.zero_le _, Nat.zero_le _⟩)
    (fun _ _ ↦ Subsingleton.elim _ _)

def excisionGridCoreIdentityCone : JoinCone (𝟙 (nerve ExcisionGridCoreIndex.{u})) :=
  ⟨nerveInitialCone excisionGridCoreSourceInitial.{u},
    nerveInitialCone_inr excisionGridCoreSourceInitial.{u}⟩

lemma excisionGridCoreIdentityCone_vertex :
    excisionGridCoreIdentityCone.{u}.vertex = nerveVertex (excisionGridCorePoint 0 0) := by
  rw [JoinCone.vertex_eq]
  have h := congrArg (fun q ↦ joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ q)
    (nerveInitialCone_at_point excisionGridCoreSourceInitial.{u})
  rw [← Category.assoc, joinInl_joinMap, Category.id_comp, SSet.comp_const] at h
  change SSet.yonedaEquiv (joinInl Δ[0] (nerve ExcisionGridCoreIndex.{u}) ≫
    nerveInitialCone excisionGridCoreSourceInitial.{u}) = _
  rw [h]
  rfl

def excisionCorePuncturedSourceCone {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    JoinCone (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) ≫ F) :=
  (F2.restrictJoinCone excisionGridCoreIdentityCone.{u}
    (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured))).postcomp F

lemma excisionCorePuncturedSourceCone_vertex {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X) :
    (excisionCorePuncturedSourceCone F).vertex =
      F.app (Opposite.op ⦋0⦌) (nerveVertex (excisionGridCorePoint 0 0)) := by
  change ((F2.restrictJoinCone excisionGridCoreIdentityCone.{u}
    (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured))).postcomp F).vertex = _
  rw [JoinCone.vertex_postcomp, F2.restrictJoinCone_vertex,
    excisionGridCoreIdentityCone_vertex]

end SerrePositivity.InfinityCategories
