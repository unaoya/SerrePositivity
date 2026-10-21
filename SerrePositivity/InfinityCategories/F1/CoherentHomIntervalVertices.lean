module

public import SerrePositivity.InfinityCategories.F1.CoherentHomIntervalNaturality
public import SerrePositivity.InfinityCategories.F1.CoherentHomComparisonVertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaceIntervalVertices
public import SerrePositivity.InfinityCategories.F1.IntervalMappingVertexEquivalence

/-!
概要：標準の coherent 区間 Hom 比較の指定頂点を元の通常の射で同定する。
方針：右 Hom 比較の零単体と、pinched・区間比較の頂点の式を合成する。
規約：局所 Kan 性は不要で、元の同じ比較の頂点を保持する。
使われ方：固定成分比較における標準の合成三角形の指定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 標準区間 Hom 比較の頂点は、元の通常の射の coherent な辺の頂点そのもの。 -/
lemma coherentHomIntervalComparison_vertex
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C}
    (s : (SimplicialCategory.sHom X Y) _⦋0⦌) :
    (coherentHomIntervalComparison X Y).app (Opposite.op ⦋0⦌) (ULift.up s) =
      intervalMappingVertexOfEdge
        (coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s)) := by
  change (pinchedHomToIntervalMappingSpace _ _).app _
    ((coherentHomComparison X Y).app _ (ULift.up s)) = _
  rw [pinchedHomToIntervalMappingSpace_vertex]
  congr 1
  apply SSet.Edge.ext
  exact coherentHomComparisonSimplex_zero_edge s

/-- 指定された同じ比較頂点から回収する辺も、元の通常の射の coherent な辺。 -/
lemma coherentHomIntervalComparison_vertex_edge
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C}
    (s : (SimplicialCategory.sHom X Y) _⦋0⦌) :
    intervalMappingEdgeOfVertex
        ((coherentHomIntervalComparison X Y).app (Opposite.op ⦋0⦌) (ULift.up s)) =
      coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s) := by
  rw [coherentHomIntervalComparison_vertex]
  exact (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _

end SerrePositivity.InfinityCategories
