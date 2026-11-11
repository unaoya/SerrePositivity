module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeDiagramEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeDiagramUpperTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeTetrahedronSides
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CosliceTransport

/-!
概要：Kan 図式の上側の比較三角形と三辺。
方針：全錐の同じ指定円柱を形状の射で制限する。
規約：図式の射と図式成分の成分を厳密に保持する。
使われ方：三つの比較三単体の合成関係の照合。
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
  (T : SSet.Homotopy c.val d.val)
/-- 概要：指定図式円柱の上側の三角形。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
def kanConeDiagramUpperTriangle
    {i j : I} (f : i ⟶ j) : SpaceInfinity.{u} _⦋2⦌ :=
  coneDiagramUpperTriangle T
    (uliftTruncatedEdge (nerve.edgeMk f).toTruncated)
/-- 概要：底辺は比較先の図式の指定射。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
lemma kanConeDiagramUpperTriangle_zero
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 0 (kanConeDiagramUpperTriangle T f) =
      (coherentNerveEdge (G.map f)).edge :=
  (coneDiagramUpperTriangle_zero _ _).trans (strictCoherentDiagram_edge _ f)
/-- 概要：長辺は図式側の共通の対角関手。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
lemma kanConeDiagramUpperTriangle_one
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 1 (kanConeDiagramUpperTriangle T f) =
      (coherentNerveEdge (kanConeDiagramDiagonal T f)).edge :=
  (coneDiagramUpperTriangle_one _ _).trans (kanConeDiagramDiagonal_edge T f).symm
/-- 概要：最初の辺は図式成分の始域での指定成分。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
lemma kanConeDiagramUpperTriangle_two
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 2 (kanConeDiagramUpperTriangle T f) =
      (coherentNerveEdge (kanConeDiagramComponent T i)).edge :=
  (coneDiagramUpperTriangle_two _ _).trans (kanConeDiagramComponent_edge T i).symm
/-- 概要：中央の比較三単体の図式側の面は指定された上側の三角形。
方針：円柱の側面の式を指定図式の辺に適用する。
規約：元の二単体の厳密な等式。
使われ方：四面の合成則へ図式側の指定同型を代入する。 -/
lemma kanConeDiagramUpperTriangle_tetrahedron
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 0 (kanConeTetrahedron T f 1) =
      kanConeDiagramUpperTriangle T f :=
  (kanConeTetrahedron_upper_last T f).trans (by rfl)

end SerrePositivity.InfinityCategories.F2
