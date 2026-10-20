module

public import SerrePositivity.InfinityCategories.F2.KanConeSecondInteriorIso
public import SerrePositivity.InfinityCategories.F2.KanConeDiagramComparisonIsos
public import SerrePositivity.InfinityCategories.F2.KanConeFirstTetrahedronRelation
public import SerrePositivity.InfinityCategories.F2.KanConeLowerIso

/-!
概要：中央の比較三単体の指定同型の合成関係。
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
/-- 概要：中央の四面の指定同型の合成は二つの内部同型を介して可換。
方針：元の三角形と六辺を揃えて四面の合成則を使う。
規約：共有面の同型の値を変更しない。
使われ方：三つの関係を合わせて各脚の比較の整合式を導く。 -/
lemma kanConeMiddleTetrahedron_relation
    {i j : I} (f : i ⟶ j) :
    kanConeSecondInteriorIso T K hc f ≪≫
        (kanConeDiagramUpperIso T f).precomp
          (show K.obj ⟶ (F.obj i).obj from
            kanNativeConeLeg c K hc i) =
      kanConeFirstInteriorIso T K hc f ≪≫
        (kanConeLowerIso T K hc i).postcomp
          (G.map f) := by
  exact spaceInfinityTetrahedronIso_square_of_edges
    (kanNativeConeLeg c K hc i) (kanConeDiagramComponent T i)
    (G.map f) (kanConeHomotopyDiagonal T K hc i)
    (kanConeDiagramDiagonal T f) (kanConeHomotopyDiagonal T K hc j)
    (kanConeTetrahedron T f 1)
    (kanConeMiddle_edge01 T K hc f) (kanConeMiddle_edge12 T f)
    (kanConeMiddle_edge23 T f) (kanConeMiddle_edge02 T K hc f)
    (kanConeMiddle_edge13 T f) (kanConeMiddle_edge03 T K hc f)
    _ _ _ _ (kanConeSecondInteriorIso_heq T K hc f)
    ((kanConeDiagramUpperIso_heq T f).trans
      (spaceInfinityTriangleIso_heq (kanConeDiagramUpperTriangle_tetrahedron T f)).symm)
    ((kanConeFirstInteriorIso_heq T K hc f).trans
      (spaceInfinityTriangleIso_heq (kanConeTetrahedron_glue_first T f)))
    ((kanConeLowerIso_heq T K hc i).trans
      (spaceInfinityTriangleIso_heq (kanConeTetrahedron_lower_first T f)).symm)

end SerrePositivity.InfinityCategories.F2
