module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeMiddleDiagonalEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.TetrahedronEdgeFaces
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleIsoFacesEquality

/-!
概要：中央と最後の比較三単体の共有面からの指定内部同型。
方針：指定円柱の実際の三単体と共有面の式を使う。
規約：同型の存在でなく指定同型の合成の等式を保持する。
使われ方：二射影の指定比較同型と指定 path の照合。
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
/-- 概要：元の脚と図式側の対角射の合成へ向かう第二の指定内部同型。
方針：元の三角形と六辺を揃えて四面の合成則を使う。
規約：共有面の同型の値を変更しない。
使われ方：三つの関係を合わせて各脚の比較の整合式を導く。 -/
def kanConeSecondInteriorIso
    {i j : I} (f : i ⟶ j) :
    FunctorIso (kanConeHomotopyDiagonal T K hc j)
      (kanNativeConeLeg c K hc i ≫ kanConeDiagramDiagonal T f) :=
  spaceInfinityTriangleIso_of_faces _ _ _
    (SpaceInfinity.δ 2 (kanConeTetrahedron T f 1))
    (kanConeMiddle_edge01 T K hc f)
    ((tetrahedronEdge13_eq _).trans (kanConeMiddle_edge13 T f))
    (kanConeMiddle_edge03 T K hc f)
/-- 概要：第二の指定内部同型は元の共有面の同型と型を含めて等しい。
方針：元の三角形と六辺を揃えて四面の合成則を使う。
規約：共有面の同型の値を変更しない。
使われ方：三つの関係を合わせて各脚の比較の整合式を導く。 -/
lemma kanConeSecondInteriorIso_heq
    {i j : I} (f : i ⟶ j) :
    HEq (kanConeSecondInteriorIso T K hc f)
      (spaceInfinityTriangleIso (SpaceInfinity.δ 2 (kanConeTetrahedron T f 1))) :=
  spaceInfinityTriangleIso_of_faces_heq _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
