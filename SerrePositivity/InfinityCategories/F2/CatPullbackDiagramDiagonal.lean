module

public import SerrePositivity.InfinityCategories.F2.ConeDiagramDiagonalEdge
public import SerrePositivity.InfinityCategories.F2.CatPullbackConeComparisonEdges
public import SerrePositivity.InfinityCategories.F1.Universe.InvertibleEdge
public import SerrePositivity.InfinityCategories.F1.Coherent.EdgeEquiv

/-!
概要：引き戻し図式の指定円柱の対角関手。
方針：全錐の同じ指定円柱を形状の射で制限する。
規約：図式の射と切断の成分を厳密に保持する。
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

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：図式側の対角辺の両端を元と置換後の対象に揃える。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
def catPullbackDiagramDiagonalEdge (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.{u}.Edge (coherentVertex ((catPullbackDiagram p q).obj i))
      (coherentVertex ((catPullbackReplacementDiagram p q).obj j)) where
  edge := (coneDiagramDiagonalEdge (catPullbackConeHomotopy p q)
    (uliftTruncatedEdge (nerve.edgeMk f).toTruncated)).edge
  src_eq := (coneDiagramDiagonalEdge (catPullbackConeHomotopy p q)
    (uliftTruncatedEdge (nerve.edgeMk f).toTruncated)).src_eq.trans
    (HomotopyLimits.strictCoherentDiagram_vertex _ i)
  tgt_eq := (coneDiagramDiagonalEdge (catPullbackConeHomotopy p q)
    (uliftTruncatedEdge (nerve.edgeMk f).toTruncated)).tgt_eq.trans
    (HomotopyLimits.strictCoherentDiagram_vertex _ j)
/-- 概要：同じ指定対角辺を小さい圏の関手に読む。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
def catPullbackDiagramDiagonal (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    (catPullbackDiagram p q).obj i ⟶ (catPullbackReplacementDiagram p q).obj j :=
  coherentNerveEdgeToHom (catPullbackDiagramDiagonalEdge p q f)
/-- 概要：読み戻した関手は元の対角辺の一次単体を保持する。
方針：指定円柱と coherent nerve の辺の回収を使う。
規約：辺・三角形の代表を変更しない。
使われ方：中央と最後の比較三単体で同じ指定同型を使う。 -/
lemma catPullbackDiagramDiagonal_edge (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    (coherentNerveEdge (catPullbackDiagramDiagonal p q f)).edge =
      (coneDiagramDiagonalEdge (catPullbackConeHomotopy p q)
        (uliftTruncatedEdge (nerve.edgeMk f).toTruncated)).edge := by
  exact congrArg SSet.Edge.edge (coherentNerveEdge_hom (catPullbackDiagramDiagonalEdge p q f))

end SerrePositivity.InfinityCategories.F2
