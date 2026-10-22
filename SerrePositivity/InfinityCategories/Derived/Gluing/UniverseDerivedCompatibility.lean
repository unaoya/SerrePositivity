module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedLaxComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseNerveLaxComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseAugmentationVertex

/-! 一般宇宙の導来矢印族と実頂点辺を、元の同じ augmentation の像として保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingUniverseDerivedAugmentationArrowFamily_postcompose :
    dgGluingUniverseDerivedAugmentationArrowFamily R C D M =
      dgGluingUniverseAugmentationArrowFamily R C D M ≫ (ihom (Δ[1] : SSet)).map
        (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C) := by
  change curry ((β_ (Δ[1] : SSet)
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (dgNerve R (DGGluingObject R C D M)))).hom ≫
      (dgGluingUniverseAugmentationHomotopy R C D M).h ≫
      dgGluingUniverseModuleDerivedComparison.{u, v, w} R C) = _
  rw [← Category.assoc, curry_natural_right]
  rfl

lemma dgGluingUniverseDerivedAugmentationHomotopy_vertex_edge
    (X : DGGluingObject R C D M) :
    (simplicialHomotopyVertexEdge (dgGluingUniverseDerivedAugmentationHomotopy R C D M)
      (ULift.up (Simplex.vertex X))).edge =
    (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋1⦌)
      (ULift.up (dgClosedEdge R (RightModule R C) (dgGluingAugmentation R C D M X)).edge) := by
  change (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋1⦌)
      (simplicialHomotopyVertexEdge (dgGluingUniverseAugmentationHomotopy R C D M)
        (ULift.up (Simplex.vertex X))).edge = _
  rw [dgGluingUniverseAugmentationHomotopy_vertex_edge]

end SerrePositivity.InfinityCategories
