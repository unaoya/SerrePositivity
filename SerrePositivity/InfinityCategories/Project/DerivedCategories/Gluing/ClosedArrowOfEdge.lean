module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges

/-! 元の dg nerve の任意の端点付き辺は、同じ端点の閉射の辺に厳密に戻る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial

lemma dgGluingClosedArrowOfEdge (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
    (x y : D) (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) :
    ∃ a : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y,
      Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R D a) = b := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed b.toTruncated, ?_⟩
  apply Edge.ext
  exact congrArg Truncated.Edge.edge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_edgeClosed R D b.toTruncated)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
