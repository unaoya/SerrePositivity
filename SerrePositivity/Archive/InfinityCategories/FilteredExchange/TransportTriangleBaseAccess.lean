module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTriangleDiagram

/-!
概要：実輸送三角形の元の底の四角形を、同じ値として参照する。
方針：図式の型に保持した底をそのまま取り出す。
規約：底の族を再選択しない。使われ方：四面体の共有辺の底を照合する。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 実三角形の型に保持されている元の底の四角形。 -/
def TransportTriangleDiagram.base {E B P : SSet.{u}} {p : E ⟶ B}
    {a b d : B _⦋0⦌} {s : TransportIntervalSquare P a b d d}
    {f : P ⟶ vertexFiber p a} {g : P ⟶ vertexFiber p b} {h : P ⟶ vertexFiber p d}
    (_T : TransportTriangleDiagram p s f g h) : TransportIntervalSquare P a b d d := s

end SerrePositivity.InfinityCategories.F2
