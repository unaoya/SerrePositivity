module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeDiagramLowerTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeLowerTriangleFaces
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeFirstTetrahedronEdges
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeTriangleIsos
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TetrahedronEdgeFaces
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeLastConeEdges

/-!
概要：最後の比較三単体の指定境界関手。
方針：同じ指定円柱の面と六辺の回収を使う。
規約：元の単体と指定同型を選び直さない。
使われ方：中央と最後の比較三単体の合成関係。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {I : Type u} [SmallCategory I] {F G : I ⥤ KanObject.{u}}
  {c : JoinCone (kanDiagramCoherentNerve F)} {d : JoinCone (kanDiagramCoherentNerve G)}
  (T : SSet.Homotopy c.val d.val) (K : KanObject.{u})
  (hc : c.vertex = coherentNerveVertex K)
/-- 概要：比較三単体の辺 03 は指定境界関手の coherent 辺。
方針：側面の三角形と共有面の一致を使う。
規約：一次単体の厳密な等式。
使われ方：六つの境界関手を固定して四面の合成則を適用する。 -/
lemma kanConeLast_edge03
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 1 (SpaceInfinity.δ 2 (kanConeTetrahedron T f 2)) =
      (coherentNerveEdge (kanConeHomotopyDiagonal T K hc j)).edge :=
  (tetrahedronEdge03_eq _).symm.trans
    ((congrArg (SpaceInfinity.δ 1) (kanConeTetrahedron_lower_long T f)).trans
      (kanConeLowerTriangle_one T K hc j))
/-- 概要：比較三単体の辺 13 は指定境界関手の coherent 辺。
方針：側面の三角形と共有面の一致を使う。
規約：一次単体の厳密な等式。
使われ方：六つの境界関手を固定して四面の合成則を適用する。 -/
lemma kanConeLast_edge13
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 1 (SpaceInfinity.δ 0 (kanConeTetrahedron T f 2)) =
      (coherentNerveEdge (kanConeDiagramDiagonal T f)).edge :=
  (congrArg (SpaceInfinity.δ 1) (kanConeDiagramLowerTriangle_tetrahedron T f)).trans
    (kanConeDiagramLowerTriangle_one T f)
/-- 概要：比較三単体の辺 23 は指定境界関手の coherent 辺。
方針：側面の三角形と共有面の一致を使う。
規約：一次単体の厳密な等式。
使われ方：六つの境界関手を固定して四面の合成則を適用する。 -/
lemma kanConeLast_edge23
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 0 (SpaceInfinity.δ 0 (kanConeTetrahedron T f 2)) =
      (coherentNerveEdge (kanConeDiagramComponent T j)).edge :=
  (congrArg (SpaceInfinity.δ 0) (kanConeDiagramLowerTriangle_tetrahedron T f)).trans
    (kanConeDiagramLowerTriangle_zero T f)

end SerrePositivity.InfinityCategories.F2
