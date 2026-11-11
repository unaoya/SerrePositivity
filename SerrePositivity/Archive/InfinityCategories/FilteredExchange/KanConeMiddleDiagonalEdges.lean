module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeDiagramLowerTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeLowerTriangleFaces
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeFirstTetrahedronEdges
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeTriangleIsos
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TetrahedronEdgeFaces
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeMiddleBaseEdges

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
/-- 概要：比較三単体の辺 01 は指定境界関手の coherent 辺。
方針：側面の三角形と共有面の一致を使う。
規約：一次単体の厳密な等式。
使われ方：六つの境界関手を固定して四面の合成則を適用する。 -/
lemma kanConeMiddle_edge01
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 2 (SpaceInfinity.δ 2 (kanConeTetrahedron T f 1)) =
      (coherentNerveEdge (kanNativeConeLeg c K hc i)).edge :=
  (tetrahedronEdge01_eq _).symm.trans
    ((congrArg (SpaceInfinity.δ 2) (kanConeTetrahedron_lower_first T f)).trans
      (kanConeLowerTriangle_two T K hc i))
/-- 概要：比較三単体の辺 02 は指定境界関手の coherent 辺。
方針：側面の三角形と共有面の一致を使う。
規約：一次単体の厳密な等式。
使われ方：六つの境界関手を固定して四面の合成則を適用する。 -/
lemma kanConeMiddle_edge02
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 1 (SpaceInfinity.δ 3 (kanConeTetrahedron T f 1)) =
      (coherentNerveEdge (kanConeHomotopyDiagonal T K hc i)).edge :=
  (congrArg (SpaceInfinity.δ 1) (kanConeTetrahedron_lower_first T f)).trans
    (kanConeLowerTriangle_one T K hc i)
/-- 概要：比較三単体の辺 03 は指定境界関手の coherent 辺。
方針：側面の三角形と共有面の一致を使う。
規約：一次単体の厳密な等式。
使われ方：六つの境界関手を固定して四面の合成則を適用する。 -/
lemma kanConeMiddle_edge03
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 1 (SpaceInfinity.δ 2 (kanConeTetrahedron T f 1)) =
      (coherentNerveEdge (kanConeHomotopyDiagonal T K hc j)).edge :=
  (tetrahedronEdge03_eq _).symm.trans
    ((congrArg (SpaceInfinity.δ 1) (kanConeTetrahedron_glue_first T f)).symm.trans
      ((tetrahedronEdge03_eq _).trans (kanConeFirst_edge03 T K hc f)))

end SerrePositivity.InfinityCategories.F2
