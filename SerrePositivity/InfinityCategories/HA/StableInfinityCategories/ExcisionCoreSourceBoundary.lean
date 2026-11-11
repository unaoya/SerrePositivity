module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PullbackConeVertex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareDiagramEvaluation

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionCorePuncturedSourceCone_boundary_val
    (b : (horn 2 2 : SSet.{u}) ⟶ nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePuncturedIndex.{u})
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u})
    (hb : b ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCorePunctured) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ Q)
    (hQ : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex Q 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 0 0)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedSourceCone
      (𝟙 (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u}))) b).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone Q).val := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveCone_val_eq_of_vertex
  · rw [Category.comp_id]
    exact hb
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone_vertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedSourceCone_vertex,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pullbackCone_vertex, hQ]
    rfl

lemma excisionCorePuncturedSourceCone_boundary_postcomp_val {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X)
    (b : (horn 2 2 : SSet.{u}) ⟶ nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePuncturedIndex.{u})
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u})
    (hb : b ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCorePunctured) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ Q)
    (hQ : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex Q 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 0 0)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedSourceCone F) b).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (Q ≫ F)).val := by
  have h := congrArg (fun q ↦ q ≫ F)
    (excisionCorePuncturedSourceCone_boundary_val b Q hb hQ)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) b ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCorePunctured)) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreIdentityCone.{u}.val) ≫ 𝟙 (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u}))) ≫ F =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ Q) ≫ F at h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) b ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCorePunctured)) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreIdentityCone.{u}.val) ≫ F) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ (Q ≫ F)
  simpa only [Category.assoc, Category.comp_id] using h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
