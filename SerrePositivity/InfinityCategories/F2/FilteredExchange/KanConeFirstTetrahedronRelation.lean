module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanConeTriangleIsos
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceTetrahedronNamedIsoSquare

/-!
概要：Kan 図式上の全錐円柱の最初の三単体の指定合成則。
方針：元の六辺と四つの指定面を四面体の合成則へ代入する。
規約：共有面の同型を選び直さない。使われ方：三つの合成則からの整合式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] {F G : I ⥤ KanObject.{u}}
  {c : JoinCone (kanDiagramCoherentNerve F)} {d : JoinCone (kanDiagramCoherentNerve G)}

/-- 概要：終域への上側比較と元の錐の三角形の合成は、共有面を通る合成に等しい。
方針：元の三単体の六辺と四面の値を同時に保持して比較。
規約：存在ではなく指定値の等式。使われ方：内部同型の消去の第一関係。 -/
lemma kanConeFirstTetrahedron_relation (T : SSet.Homotopy c.val d.val)
    (K L : KanObject.{u}) (hc : c.vertex = coherentNerveVertex K)
    (hd : d.vertex = coherentNerveVertex L) (a : K ⟶ L)
    (ha : (coneHomotopyApexEdge T).edge = (coherentNerveEdge a).edge)
    {i j : I} (f : i ⟶ j) :
    kanConeUpperIso T K L hc hd a ha j ≪≫
        (kanNativeConeTriangleIso d L hd f).precomp (show K.obj ⟶ L.obj from a) =
      kanConeFirstInteriorIso T K hc f ≪≫
        (kanConeUpperIso T K L hc hd a ha i).postcomp (G.map f) := by
  exact spaceInfinityTetrahedronIso_square_of_edges a (kanNativeConeLeg d L hd i) (G.map f)
    (kanConeHomotopyDiagonal T K hc i) (kanNativeConeLeg d L hd j)
    (kanConeHomotopyDiagonal T K hc j) (kanConeTetrahedron T f 0)
    (kanConeFirst_edge01 T K L a ha f) (kanConeFirst_edge12 T L hd f)
    (kanConeFirst_edge23 T f) (kanConeFirst_edge02 T K hc f)
    (kanConeFirst_edge13 T L hd f) (kanConeFirst_edge03 T K hc f) _ _ _ _
    ((kanConeUpperIso_heq T K L hc hd a ha j).trans
      (spaceInfinityTriangleIso_heq (kanConeTetrahedron_upper_long T f)).symm)
    ((kanNativeConeTriangleIso_heq d L hd f).trans
      (spaceInfinityTriangleIso_heq (kanConeTetrahedron_first T f)).symm)
    (kanConeFirstInteriorIso_heq T K hc f)
    ((kanConeUpperIso_heq T K L hc hd a ha i).trans
      (spaceInfinityTriangleIso_heq (kanConeTetrahedron_upper_first T f)).symm)

end SerrePositivity.InfinityCategories.F2
