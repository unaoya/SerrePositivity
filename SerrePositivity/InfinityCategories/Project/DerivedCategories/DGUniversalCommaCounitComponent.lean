module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeComponent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCommaCounit
/-!
概要：一般 comma の実余単位の頂点辺を元の同じ閉射へ同定する。
方針：同じ実 prism と反対比較を、一次単体と厳密切断で評価する。
規約：同じ全関手と閉射を保持する。使われ方：一般 RHom の標準写像空間判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial

/-- 一般 comma の実余単位ホモトピーの頂点辺は、同じ普遍余単位の閉射。 -/
lemma dgUniversalCommaCounitHomotopy_vertex_edge
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
    (x : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalComma R C E F) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaCounitHomotopy R C E F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E x.label.universal.counit).edge := by
  let K := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R Cᵒᵖ Eᵒᵖ F.op
  let A := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R Cᵒᵖ Eᵒᵖ F.op
  let B := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R Cᵒᵖ Eᵒᵖ F.op
  let z := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaDualLabel R C E F x.label
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeHomotopy R K Eᵒᵖ A B
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationUnliftedHomotopy R Cᵒᵖ Eᵒᵖ F.op))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Opposite.op z))).edge.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDoubleOppositeDown R E) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeHomotopy_vertex_edge,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationUnliftedHomotopy_vertex_edge, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex_dgClosedEdge,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
