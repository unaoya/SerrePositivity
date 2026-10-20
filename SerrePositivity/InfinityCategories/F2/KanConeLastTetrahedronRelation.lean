module

public import SerrePositivity.InfinityCategories.F2.KanConeMiddleTetrahedronRelation
public import SerrePositivity.InfinityCategories.F2.KanConeLastDiagonalEdges

/-!
概要：最後の比較三単体の指定同型の合成関係。
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
/-- 概要：最後の四面の指定同型の合成は元の錐の三角形と下側の比較に一致。
方針：元の三角形と六辺を揃えて四面の合成則を使う。
規約：共有面の同型の値を変更しない。
使われ方：三つの関係を合わせて各脚の比較の整合式を導く。 -/
lemma kanConeLastTetrahedron_relation
    {i j : I} (f : i ⟶ j) :
    kanConeSecondInteriorIso T K hc f ≪≫
        (kanConeDiagramLowerIso T f).precomp
          (show K.obj ⟶ (F.obj i).obj from
            kanNativeConeLeg c K hc i) =
      kanConeLowerIso T K hc j ≪≫
        (kanNativeConeTriangleIso c K hc f).postcomp
          (kanConeDiagramComponent T j) := by
  exact spaceInfinityTetrahedronIso_square_of_edges
    (kanNativeConeLeg c K hc i) (F.map f)
    (kanConeDiagramComponent T j) (kanNativeConeLeg c K hc j)
    (kanConeDiagramDiagonal T f) (kanConeHomotopyDiagonal T K hc j)
    (kanConeTetrahedron T f 2)
    (kanConeLast_edge01 T K hc f) (kanConeLast_edge12 T f)
    (kanConeLast_edge23 T f) (kanConeLast_edge02 T K hc f)
    (kanConeLast_edge13 T f) (kanConeLast_edge03 T K hc f)
    _ _ _ _
    ((kanConeSecondInteriorIso_heq T K hc f).trans
      (spaceInfinityTriangleIso_heq (kanConeTetrahedron_glue_last T f)))
    ((kanConeDiagramLowerIso_heq T f).trans
      (spaceInfinityTriangleIso_heq (kanConeDiagramLowerTriangle_tetrahedron T f)).symm)
    ((kanConeLowerIso_heq T K hc j).trans
      (spaceInfinityTriangleIso_heq (kanConeTetrahedron_lower_long T f)).symm)
    ((kanNativeConeTriangleIso_heq c K hc f).trans
      (spaceInfinityTriangleIso_heq (kanConeTetrahedron_last T f)).symm)

end SerrePositivity.InfinityCategories.F2
