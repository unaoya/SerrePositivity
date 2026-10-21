module
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
/-!
概要：実ホモトピーの入力制限は、同じ頂点の辺を厳密に回収する。
方針：退化恒等辺の写像公式を、元の円柱上の実一次単体へ代入する。
規約：辺を選び直さない。使われ方：出力分解 augmentation の準同型条件。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
/-- 入力前合成後の実頂点辺は、元の入力像での同じ実頂点辺。 -/
lemma simplicialHomotopyVertexEdge_precomp_edge {A B X : SSet.{u}} {f g : B ⟶ X}
    (H : SSet.Homotopy f g) (i : A ⟶ B) (a : A _⦋0⦌) :
    (simplicialHomotopyVertexEdge (functorHomotopyPrecomp H i) a).edge =
      (simplicialHomotopyVertexEdge H (i.app (Opposite.op ⦋0⦌) a)).edge := by
  have hid := congrArg SSet.Truncated.Edge.edge
    (SSet.Truncated.Edge.map_id a ((truncation 2).map i))
  change H.h.app (Opposite.op ⦋1⦌)
    (i.app (Opposite.op ⦋1⦌) (SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge,
      homotopyIntervalEdge.edge) =
    H.h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj B) (i.app (Opposite.op ⦋0⦌) a)).edge,
        homotopyIntervalEdge.edge)
  rw [show i.app (Opposite.op ⦋1⦌)
    (SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge = _ from hid]
  rfl
end SerrePositivity.InfinityCategories
