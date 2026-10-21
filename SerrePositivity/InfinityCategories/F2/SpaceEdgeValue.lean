module

public import SerrePositivity.InfinityCategories.F2.SpaceLeftHomValue
public import SerrePositivity.InfinityCategories.F1.CoherentEdgeEquiv

/-!
概要：任意の指定空間辺を、その元の両頂点の Kan 値の間の射へ厳密に読み戻す。
方針：頂点の回収等式で両端を合わせ、coherent nerve の辺と射の全単射を使う。
規約：全一単体を保持。使われ方：両端固定の比較円柱と全三角形の値の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定空間辺を、元の両頂点の Kan 値の間の射に読み戻す。 -/
def spaceInfinityEdgeValue {x y : SpaceInfinity.{u} _⦋0⦌} (e : SpaceInfinity.{u}.Edge x y) :
    spaceInfinityObject x ⟶ spaceInfinityObject y :=
  coherentNerveEdgeToHom (e.ofEq (coherentNerveVertex_object x).symm
    (coherentNerveVertex_object y).symm)

/-- Kan 値の射から coherent 辺へ戻すと、元の全一単体が厳密に回収される。 -/
lemma spaceInfinityEdgeValue_edge {x y : SpaceInfinity.{u} _⦋0⦌}
    (e : SpaceInfinity.{u}.Edge x y) :
    (coherentNerveEdge (spaceInfinityEdgeValue e)).edge = e.edge :=
  congrArg SSet.Edge.edge (coherentNerveEdge_hom _)

/-- 元の頂点の Kan 値の恒等辺は、同じ頂点の定値区間の全一単体。 -/
lemma spaceInfinityIdentity_edge (x : SpaceInfinity.{u} _⦋0⦌) :
    (coherentNerveEdge (𝟙 (spaceInfinityObject x))).edge =
      SSet.yonedaEquiv (SSet.const x : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u}) := by
  have hi := congrArg SSet.Edge.edge (coherentNerveEdge_id (spaceInfinityObject x))
  have hv := congrArg (fun v : SpaceInfinity.{u} _⦋0⦌ => (SSet.Edge.id v).edge)
    (coherentNerveVertex_object x)
  exact hi.trans (hv.trans (pinchedConstant_one (X := SpaceInfinity.{u}) x).symm)

end SerrePositivity.InfinityCategories.F2
