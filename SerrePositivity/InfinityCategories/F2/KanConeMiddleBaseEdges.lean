module

public import SerrePositivity.InfinityCategories.F2.KanConeDiagramLowerTriangle
public import SerrePositivity.InfinityCategories.F2.KanConeLowerTriangleFaces
public import SerrePositivity.InfinityCategories.F2.KanConeFirstTetrahedronEdges
public import SerrePositivity.InfinityCategories.F2.KanConeTriangleIsos
public import SerrePositivity.InfinityCategories.F2.TetrahedronEdgeFaces

/-!
概要：中央の比較三単体の指定境界関手。
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
/-- 概要：比較三単体の辺 12 は指定境界関手の coherent 辺。
方針：側面の三角形と共有面の一致を使う。
規約：一次単体の厳密な等式。
使われ方：六つの境界関手を固定して四面の合成則を適用する。 -/
lemma kanConeMiddle_edge12
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 2 (SpaceInfinity.δ 0 (kanConeTetrahedron T f 1)) =
      (coherentNerveEdge (kanConeDiagramComponent T i)).edge :=
  (congrArg (SpaceInfinity.δ 2) (kanConeDiagramUpperTriangle_tetrahedron T f)).trans
    (kanConeDiagramUpperTriangle_two T f)
/-- 概要：比較三単体の辺 13 は指定境界関手の coherent 辺。
方針：側面の三角形と共有面の一致を使う。
規約：一次単体の厳密な等式。
使われ方：六つの境界関手を固定して四面の合成則を適用する。 -/
lemma kanConeMiddle_edge13
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 1 (SpaceInfinity.δ 0 (kanConeTetrahedron T f 1)) =
      (coherentNerveEdge (kanConeDiagramDiagonal T f)).edge :=
  (congrArg (SpaceInfinity.δ 1) (kanConeDiagramUpperTriangle_tetrahedron T f)).trans
    (kanConeDiagramUpperTriangle_one T f)
/-- 概要：比較三単体の辺 23 は指定境界関手の coherent 辺。
方針：側面の三角形と共有面の一致を使う。
規約：一次単体の厳密な等式。
使われ方：六つの境界関手を固定して四面の合成則を適用する。 -/
lemma kanConeMiddle_edge23
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 0 (SpaceInfinity.δ 0 (kanConeTetrahedron T f 1)) =
      (coherentNerveEdge (G.map f)).edge :=
  (congrArg (SpaceInfinity.δ 0) (kanConeDiagramUpperTriangle_tetrahedron T f)).trans
    (kanConeDiagramUpperTriangle_zero T f)

end SerrePositivity.InfinityCategories.F2
