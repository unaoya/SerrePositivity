module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTetrahedronWhiskerEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.EdgeSquareOfEdgeEquality

/-!
概要：同じ六関手で表した四面の指定辺の可換正方形。
方針：四つの辺の端点を同時に輸送する。
規約：元の一単体とそのホモトピー類を保つ。
使われ方：指定関手同型の前後合成の式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：四面の指定辺の前後合成は共通の四つの関手の間で可換。
方針：各一単体の同定から四頂点の等式を回収し、正方形を輸送する。
規約：合成の終点を括弧付け (01 ≫ 12) ≫ 23 に統一する。
使われ方：元の四面の関手同型の合成則。 -/
lemma spaceInfinityTetrahedron_triangle_square (s : SpaceInfinity.{u} _⦋3⦌) :
    SSet.Truncated.HomotopyCategory.homMk (spaceInfinityTetrahedronTriangle013 s).toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk (spaceInfinityTetrahedronPre123 s).toTruncated =
    SSet.Truncated.HomotopyCategory.homMk (spaceInfinityTetrahedronTriangle023 s).toTruncated ≫
      SSet.Truncated.HomotopyCategory.homMk (spaceInfinityTetrahedronPost012 s).toTruncated := by
  exact homMk_square_of_edge_eq
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine013).toTruncated
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine013Full).toTruncated
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine023).toTruncated
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine023Full).toTruncated
    (spaceInfinityTetrahedronTriangle013 s).toTruncated
    (spaceInfinityTetrahedronPre123 s).toTruncated
    (spaceInfinityTetrahedronTriangle023 s).toTruncated
    (spaceInfinityTetrahedronPost012 s).toTruncated
    (coherentTetrahedronHom_square s) rfl
    (spaceInfinityTetrahedronPre123_edge s) rfl
    (spaceInfinityTetrahedronPost012_edge s)

end SerrePositivity.InfinityCategories.F2
