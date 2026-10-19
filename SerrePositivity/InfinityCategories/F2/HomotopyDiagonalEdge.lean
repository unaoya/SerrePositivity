module

public import SerrePositivity.InfinityCategories.F2.HomotopySimplexFaces

/-!
概要：指定円柱の対角辺。
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

/-- 概要：空間の辺と時刻の辺を同時に通る円柱の対角辺。
方針：円柱の単体と既存の辺の面の式を使う。
規約：元の一次単体・二単体を保持する。
使われ方：錐の指定された比較三角形の関手同型への移行。 -/
def homotopyDiagonalEdge {X Y : SSet.{u}} {f g : X ⟶ Y}
    (G : SSet.Homotopy f g) {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    Y.Edge (f.app (Opposite.op ⦋0⦌) x) (g.app (Opposite.op ⦋0⦌) y) := by
  let m := (e.tensor homotopyIntervalEdge).map ((truncation 2).map G.h)
  refine SSet.Edge.mk m.edge ?_ ?_
  · exact m.src_eq.trans (ConcreteCategory.congr_hom
      (NatTrans.congr_app G.h₀ (Opposite.op ⦋0⦌)) x)
  · exact m.tgt_eq.trans (ConcreteCategory.congr_hom
      (NatTrans.congr_app G.h₁ (Opposite.op ⦋0⦌)) y)
/-- 概要：対角辺の一次単体は元の空間の辺と区間の恒等辺の像。
方針：円柱の単体と既存の辺の面の式を使う。
規約：元の一次単体・二単体を保持する。
使われ方：錐の指定された比較三角形の関手同型への移行。 -/
lemma homotopyDiagonalEdge_simplex {X Y : SSet.{u}} {f g : X ⟶ Y}
    (G : SSet.Homotopy f g) {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    (homotopyDiagonalEdge G e).edge =
      G.h.app (Opposite.op ⦋1⦌) (e.edge, SSet.yonedaEquiv (𝟙 Δ[1])) := by
  change G.h.app (Opposite.op ⦋1⦌) (e.edge, homotopyIntervalEdge.edge) = _
  rw [homotopyIntervalEdge_simplex]

end SerrePositivity.InfinityCategories.F2
