module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseAugmentationPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaPrismUnitEdge

/-! 共通単体宇宙へ移した構造変換の実頂点辺も、元の augmentation の持ち上げ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)

lemma dgGluingUniverseAugmentationHomotopy_vertex_edge
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseAugmentationHomotopy R C D M)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))).edge =
    ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (RightModule R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseAugmentationPrism R C D M).app (Opposite.op ⦋1⦌)
    ((Truncated.Edge.id (X := (truncation 2).obj
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)))) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))).edge,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
  have hi : (Truncated.Edge.id (X := (truncation 2).obj
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)))) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))).edge =
      ULift.up (Truncated.Edge.id (X := (truncation 2).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)).edge := rfl
  rw [hi]
  change ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R D (RightModule R C) M.toFunctor
    ((Truncated.Edge.id (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)).edge.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M))
    (stdSimplex.objEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{max (u + 1) v w}).edge).toOrderHom) = _
  have hb : (stdSimplex.objEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{max (u + 1) v w}).edge).toOrderHom = OrderHom.id := by
    ext i
    fin_cases i <;> rfl
  rw [hb, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve_vertex_identity_simplex,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplex_unit_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPrism_unitEdge]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
