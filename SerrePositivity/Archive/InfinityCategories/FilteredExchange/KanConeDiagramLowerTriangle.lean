module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeDiagramUpperTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeDiagramLowerTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeTetrahedronSides

/-!
概要：Kan 図式の下側の比較三角形と三辺。
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
/-- 概要：同じ指定図式円柱の下側の三角形。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
def kanConeDiagramLowerTriangle
    {i j : I} (f : i ⟶ j) : SpaceInfinity.{u} _⦋2⦌ :=
  coneDiagramLowerTriangle T
    (uliftTruncatedEdge (nerve.edgeMk f).toTruncated)
/-- 概要：最後の辺は図式成分の終域での指定成分。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
lemma kanConeDiagramLowerTriangle_zero
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 0 (kanConeDiagramLowerTriangle T f) =
      (coherentNerveEdge (kanConeDiagramComponent T j)).edge :=
  (coneDiagramLowerTriangle_zero _ _).trans (kanConeDiagramComponent_edge T j).symm
/-- 概要：長辺は同じ共通の対角関手。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
lemma kanConeDiagramLowerTriangle_one
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 1 (kanConeDiagramLowerTriangle T f) =
      (coherentNerveEdge (kanConeDiagramDiagonal T f)).edge :=
  (coneDiagramLowerTriangle_one _ _).trans (kanConeDiagramDiagonal_edge T f).symm
/-- 概要：最初の辺は元の図式の指定射。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
lemma kanConeDiagramLowerTriangle_two
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 2 (kanConeDiagramLowerTriangle T f) =
      (coherentNerveEdge (F.map f)).edge :=
  (coneDiagramLowerTriangle_two _ _).trans (strictCoherentDiagram_edge _ f)
/-- 概要：最後の比較三単体の図式側の面は指定された下側の三角形。
方針：円柱の側面の式を指定図式の辺に適用する。
規約：元の二単体の厳密な等式。
使われ方：四面の合成則へ図式側の指定同型を代入する。 -/
lemma kanConeDiagramLowerTriangle_tetrahedron
    {i j : I} (f : i ⟶ j) :
    SpaceInfinity.δ 0 (kanConeTetrahedron T f 2) =
      kanConeDiagramLowerTriangle T f :=
  (kanConeTetrahedron_lower_last T f).trans (by rfl)

end SerrePositivity.InfinityCategories.F2
