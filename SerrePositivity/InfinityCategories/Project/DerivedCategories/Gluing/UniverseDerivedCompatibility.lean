module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseDerivedLaxComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseNerveLaxComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseAugmentationVertex

/-! 一般宇宙の導来矢印族と実頂点辺を、元の同じ augmentation の像として保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)

lemma dgGluingUniverseDerivedAugmentationArrowFamily_postcompose :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedAugmentationArrowFamily R C D M =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseAugmentationArrowFamily R C D M ≫ (ihom (Δ[1] : SSet)).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C) := by
  change curry ((β_ (Δ[1] : SSet)
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)))).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseAugmentationHomotopy R C D M).h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C) = _
  rw [← Category.assoc, curry_natural_right]
  rfl

lemma dgGluingUniverseDerivedAugmentationHomotopy_vertex_edge
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedAugmentationHomotopy R C D M)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))).edge =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋1⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (RightModule R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)).edge) := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseAugmentationHomotopy R C D M)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseAugmentationHomotopy_vertex_edge]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
