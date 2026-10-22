module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedNerveLaxComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.NerveAugmentationVertex

/-! 導来比較の全矢印族と頂点辺は、元の同じ比較の β5 出力分解像。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C] [DGCategory R D]
  (M : Bimodule R C D)

lemma dgGluingDerivedAugmentationArrowFamily_postcompose :
    dgGluingDerivedAugmentationArrowFamily R C D M =
      dgGluingAugmentationArrowFamily R C D M ≫
        (ihom (Δ[1] : SSet)).map (dgGluingModuleDerivedComparison R C) := by
  change curry ((β_ (Δ[1] : SSet) (dgNerve R (DGGluingObject R C D M))).hom ≫
      (dgGluingAugmentationNerveHomotopy R C D M).h ≫
      dgGluingModuleDerivedComparison R C) = _
  rw [← Category.assoc, curry_natural_right]
  rfl

lemma dgGluingDerivedAugmentationHomotopy_vertex_edge
    (X : DGGluingObject R C D M) :
    (simplicialHomotopyVertexEdge (dgGluingDerivedAugmentationHomotopy R C D M)
      (Simplex.vertex X)).edge =
    (dgGluingModuleDerivedComparison R C).app (Opposite.op ⦋1⦌)
      (dgClosedEdge R (RightModule R C) (dgGluingAugmentation R C D M X)).edge := by
  change (dgGluingModuleDerivedComparison R C).app (Opposite.op ⦋1⦌)
      (simplicialHomotopyVertexEdge (dgGluingAugmentationNerveHomotopy R C D M)
        (Simplex.vertex X)).edge = _
  rw [dgGluingAugmentationNerveHomotopy_vertex_edge]

end SerrePositivity.InfinityCategories
