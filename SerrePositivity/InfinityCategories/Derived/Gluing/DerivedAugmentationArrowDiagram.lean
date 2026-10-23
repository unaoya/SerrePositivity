module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxComparisonVertexImage
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalFamilyVertexEdge

/-! 元の構造矢印族の頂点を、同じ閉 augmentation の導来像の実区間図式に同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedAugmentationArrowDiagram (X : DGGluingObject R C D M) :
    (Δ[1] : SSet.{max (u + 1) v w}) ⟶
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (dgModuleDerivedInfinityCategory R C) :=
  SSet.yonedaEquiv.symm
    ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋1⦌)
      (ULift.up (dgClosedEdge R (RightModule R C) (dgGluingAugmentation R C D M X)).edge))

lemma dgGluingDerivedAugmentationArrowDiagram_vertex (X : DGGluingObject R C D M) :
    (dgGluingUniverseDerivedAugmentationArrowFamily R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex X)) =
      functorVertex (dgGluingDerivedAugmentationArrowDiagram R C D M X) := by
  apply intervalFunctorVertexEdge_injective
  rw [dgGluingUniverseDerivedAugmentationArrowFamily, dgGluingCurryHomotopy_vertex_edge,
    dgGluingUniverseDerivedAugmentationHomotopy_vertex_edge,
    intervalFunctorVertexEdge_functorVertex, dgGluingDerivedAugmentationArrowDiagram,
    Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories
