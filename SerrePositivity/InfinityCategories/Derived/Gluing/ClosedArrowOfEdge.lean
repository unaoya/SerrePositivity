module
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges

/-! 元の dg nerve の任意の端点付き辺は、同じ端点の閉射の辺に厳密に戻る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial

lemma dgGluingClosedArrowOfEdge (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
    (x y : D) (b : (dgNerve R D).Edge (Simplex.vertex x) (Simplex.vertex y)) :
    ∃ a : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y,
      Edge.ofTruncated (dgClosedEdge R D a) = b := by
  refine ⟨edgeClosed b.toTruncated, ?_⟩
  apply Edge.ext
  exact congrArg Truncated.Edge.edge (dgClosedEdge_edgeClosed R D b.toTruncated)

end SerrePositivity.InfinityCategories
