module

public import SerrePositivity.InfinityCategories.F2.KanConeTetrahedra

/-!
概要：全錐円柱の最初の三単体の六辺を元の Kan 射へ照合する。
方針：元の上面と側面の辺を読む。
規約：頂点比較と対角射を保持。使われ方：指定された第一の合成則。
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
  (T : SSet.Homotopy c.val d.val) (K L : KanObject.{u})
  (hc : c.vertex = coherentNerveVertex K) (hd : d.vertex = coherentNerveVertex L)

/-- 概要：辺 12 は比較先の元の脚。
方針：上面の最初の辺。規約：全一単体。使われ方：六辺の同定。 -/
lemma kanConeFirst_edge12 {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 2 (SpaceInfinity.δ 0 (kanConeTetrahedron T f 0)) =
      (coherentNerveEdge (kanNativeConeLeg d L hd i)).edge :=
  (congrArg (SpaceInfinity.δ 2) (kanConeTetrahedron_first T f)).trans
    (kanNativeConeTriangle_two d L hd f)

/-- 概要：辺 13 は比較先の元の終域への脚。
方針：上面の長辺。規約：全一単体。使われ方：六辺の同定。 -/
lemma kanConeFirst_edge13 {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 1 (SpaceInfinity.δ 0 (kanConeTetrahedron T f 0)) =
      (coherentNerveEdge (kanNativeConeLeg d L hd j)).edge :=
  (congrArg (SpaceInfinity.δ 1) (kanConeTetrahedron_first T f)).trans
    (kanNativeConeTriangle_one d L hd f)

/-- 概要：辺 23 は比較先の元の図式射。
方針：上面の底辺。規約：全一単体。使われ方：六辺の同定。 -/
lemma kanConeFirst_edge23 {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 0 (SpaceInfinity.δ 0 (kanConeTetrahedron T f 0)) =
      (coherentNerveEdge (G.map f)).edge :=
  (congrArg (SpaceInfinity.δ 0) (kanConeTetrahedron_first T f)).trans
    (kanNativeConeTriangle_zero d f)

/-- 概要：辺 01 は元の頂点比較射。
方針：長い側面の最初の辺。規約：元の比較。使われ方：六辺の同定。 -/
lemma kanConeFirst_edge01 (a : K ⟶ L)
    (ha : (coneHomotopyApexEdge T).edge = (coherentNerveEdge a).edge)
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 2 (SpaceInfinity.δ 2 (kanConeTetrahedron T f 0)) =
      (coherentNerveEdge a).edge :=
  (congrArg (SpaceInfinity.δ 2) (kanConeTetrahedron_upper_long T f)).trans
    ((coneHomotopyUpperTriangle_two T _).trans ha)

/-- 概要：辺 02 は始域側の元の対角射。
方針：短い側面の長辺。規約：元の円柱。使われ方：六辺の同定。 -/
lemma kanConeFirst_edge02 {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 1 (SpaceInfinity.δ 3 (kanConeTetrahedron T f 0)) =
      (coherentNerveEdge (kanConeHomotopyDiagonal T K hc i)).edge :=
  (congrArg (SpaceInfinity.δ 1) (kanConeTetrahedron_upper_first T f)).trans
    ((coneHomotopyUpperTriangle_one T _).trans (kanConeHomotopyDiagonal_edge T K hc i).symm)

/-- 概要：辺 03 は終域側の元の対角射。
方針：長い側面の長辺。規約：元の円柱。使われ方：六辺の同定。 -/
lemma kanConeFirst_edge03 {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 1 (SpaceInfinity.δ 2 (kanConeTetrahedron T f 0)) =
      (coherentNerveEdge (kanConeHomotopyDiagonal T K hc j)).edge :=
  (congrArg (SpaceInfinity.δ 1) (kanConeTetrahedron_upper_long T f)).trans
    ((coneHomotopyUpperTriangle_one T _).trans (kanConeHomotopyDiagonal_edge T K hc j).symm)

end SerrePositivity.InfinityCategories.F2
