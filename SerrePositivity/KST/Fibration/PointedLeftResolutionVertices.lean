module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.PointedLeftResolutionVertices
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.PointedLeftResolutionVertices
public import SerrePositivity.KST.Fibration.PointKanHomVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedReverseFiberVertices

/-! # 元の左解像比較の零単体を、反転した空間の同じ元の点として回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 元の標準 Hom 係数で reverse 比較を評価すると、その同じ元の点を回収する。 -/
theorem pointedReverseKanFiberComparison_point (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (v : K.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv K
      ((show ((SSet.uliftFunctor.{u + 1, u}).obj
          (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K)).op ⟶
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K) from
              _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedReverseKanFiberComparison K).app (Opposite.op ⦋0⦌)
        (SSet.opObjEquiv.symm (ULift.up
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso K).inv.app (Opposite.op ⦋0⦌) v)))) = v := by
  rw [pointKanObjectHomIso_inv_vertex]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedReverseKanFiberComparison_vertex K
    (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject ⟶ K from SSet.yonedaEquiv.symm v)
  rw [kanObject_homEquiv'_functorVertex] at h
  dsimp only [SimplicialCategory.sHom, EnrichedCategory.Hom, EnrichedCategory.opposite,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanObject_enrichedCategory] at h ⊢
  simpa only [Equiv.apply_symm_apply] using h

/-- 左解像比較の元の係数点の像は、標準 pointed 頂点として反転した同じ点を回収する。 -/
theorem pointedSpaceLeftResolutionComparison_vertex (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (v : K.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj K)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftResolutionComparison K).app (Opposite.op ⦋0⦌) (ULift.up v)) =
        SSet.opObjEquiv.symm v := by
  have h := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (ULift.up v))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedReverseKanFiberComparison_resolution K)
  simp only [NatTrans.comp_app_apply] at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.uliftMapVertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.uliftOppositeVertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.pointedSpaceLeftCoefficientIso_vertex,
    Equiv.apply_symm_apply] at h
  have he := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj K)) h
  have hp := pointedReverseKanFiberComparison_point
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj K) (SSet.opObjEquiv.symm v)
  dsimp only [SimplicialCategory.sHom, EnrichedCategory.Hom, EnrichedCategory.opposite,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.kanObject_enrichedCategory] at he hp
  exact he.symm.trans hp

/-- 左解像比較の実頂点は、反転した同じ元の点の標準 pointed 表示そのもの。 -/
theorem pointedSpaceLeftResolutionComparison_vertex_eq (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (v : K.obj _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftResolutionComparison K).app (Opposite.op ⦋0⦌) (ULift.up v) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj K)).symm
        (SSet.opObjEquiv.symm v) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj K)).injective
  rw [pointedSpaceLeftResolutionComparison_vertex, Equiv.apply_symm_apply]

end SerrePositivity.KST.Fibration
