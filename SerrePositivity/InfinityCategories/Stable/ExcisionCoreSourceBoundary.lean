module
public import SerrePositivity.InfinityCategories.Stable.PullbackConeVertex
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

lemma excisionCorePuncturedSourceCone_boundary_val
    (b : (horn 2 2 : SSet.{u}) ⟶ nerve ExcisionCorePuncturedIndex.{u})
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ nerve ExcisionGridCoreIndex.{u})
    (hb : b ≫ nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) =
      cospanSquareBoundary ≫ Q)
    (hQ : squareVertex Q 0 0 = nerveVertex (excisionGridCorePoint 0 0)) :
    (F2.restrictJoinCone (excisionCorePuncturedSourceCone
      (𝟙 (nerve ExcisionGridCoreIndex.{u}))) b).val = (pullbackCone Q).val := by
  apply thinNerveCone_val_eq_of_vertex
  · rw [Category.comp_id]
    exact hb
  · rw [F2.restrictJoinCone_vertex, excisionCorePuncturedSourceCone_vertex,
      pullbackCone_vertex, hQ]
    rfl

lemma excisionCorePuncturedSourceCone_boundary_postcomp_val {X : SSet.{u}}
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (b : (horn 2 2 : SSet.{u}) ⟶ nerve ExcisionCorePuncturedIndex.{u})
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ nerve ExcisionGridCoreIndex.{u})
    (hb : b ≫ nerveMap (posetSubtypeInclusion IsExcisionCorePunctured) =
      cospanSquareBoundary ≫ Q)
    (hQ : squareVertex Q 0 0 = nerveVertex (excisionGridCorePoint 0 0)) :
    (F2.restrictJoinCone (excisionCorePuncturedSourceCone F) b).val =
      (pullbackCone (Q ≫ F)).val := by
  have h := congrArg (fun q ↦ q ≫ F)
    (excisionCorePuncturedSourceCone_boundary_val b Q hb hQ)
  change (joinMap (𝟙 Δ[0]) b ≫
    ((joinMap (𝟙 Δ[0]) (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured)) ≫
      excisionGridCoreIdentityCone.{u}.val) ≫ 𝟙 (nerve ExcisionGridCoreIndex.{u}))) ≫ F =
        (cospanConeSquareIso.hom ≫ Q) ≫ F at h
  change joinMap (𝟙 Δ[0]) b ≫
    ((joinMap (𝟙 Δ[0]) (nerveMap (posetSubtypeInclusion IsExcisionCorePunctured)) ≫
      excisionGridCoreIdentityCone.{u}.val) ≫ F) = cospanConeSquareIso.hom ≫ (Q ≫ F)
  simpa only [Category.assoc, Category.comp_id] using h

end SerrePositivity.InfinityCategories
