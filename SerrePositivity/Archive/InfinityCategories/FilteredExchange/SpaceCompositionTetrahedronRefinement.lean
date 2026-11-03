module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionTetrahedronRefinement
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.InvertibleEdgeIsoEquality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleIso

/-!
概要：空間の合成比較三単体の第二面は元の指定円柱と指定同型を保つ。
方針：実際の Hom の一単体の一致を uncurry とホモトピー類へ移す。
規約：辺や同型を選び直さない。
使われ方：元の三角形の値比較を四面の合成則へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 第二面の指定円柱は元の指定円柱そのもの。 -/
lemma spaceCompositionTetrahedron_face_two_prism (s : SpaceInfinity.{u} _⦋2⦌) :
    (spaceInfinityTriangleHomotopy
      (SpaceInfinity.δ 2 (coherentCompositionTetrahedron s))).h =
        (spaceInfinityTriangleHomotopy s).h := by
  rw [spaceInfinityTriangleHomotopy_h, spaceInfinityTriangleHomotopy_h]
  exact congrArg (fun e ↦ MonoidalClosed.uncurry (SSet.yonedaEquiv.symm e))
    (coherentCompositionTetrahedron_face_two_homotopy s)

/-- 第二面の指定関手同型は端点を含めて元の指定関手同型と等しい。 -/
lemma spaceCompositionTetrahedron_face_two_iso (s : SpaceInfinity.{u} _⦋2⦌) :
    HEq (spaceInfinityTriangleIso
      (SpaceInfinity.δ 2 (coherentCompositionTetrahedron s))) (spaceInfinityTriangleIso s) := by
  have : IsInvertibleEdge
      (spaceInfinityTriangleEdge
        (SpaceInfinity.δ 2 (coherentCompositionTetrahedron s))).toTruncated :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  have : IsInvertibleEdge (spaceInfinityTriangleEdge s).toTruncated :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  apply invertibleEdgeIso_heq_of_edge_eq
  exact coherentCompositionTetrahedron_face_two_homotopy s

end SerrePositivity.InfinityCategories.F2
