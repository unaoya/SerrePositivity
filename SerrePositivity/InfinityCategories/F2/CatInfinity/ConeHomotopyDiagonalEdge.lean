module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.HomotopyDiagonalEdge
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeHomotopyEdges

/-!
概要：全錐の比較円柱の対角辺。
方針：元のホモトピーを標準の脚の比較正方形で制限する。
規約：辺や三角形の充填を新たに選択しない。
使われ方：同じ指定円柱から二脚の比較同型を構成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の錐の頂点から比較先の図式の指定対象への対角辺。
方針：円柱の単体と既存の辺の面の式を使う。
規約：元の一次単体・二単体を保持する。
使われ方：錐の指定された比較三角形の関手同型への移行。 -/
def coneHomotopyDiagonalEdge {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (G : SSet.Homotopy c.val d.val) (k : K _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj X) c.vertex
      (q.app (Opposite.op ⦋0⦌) k) where
  edge := (homotopyDiagonalEdge G (coneDomainLeg k)).edge
  src_eq := (homotopyDiagonalEdge G (coneDomainLeg k)).src_eq
  tgt_eq := (homotopyDiagonalEdge G (coneDomainLeg k)).tgt_eq.trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app d.property (Opposite.op ⦋0⦌)) k)

end SerrePositivity.InfinityCategories.F2
