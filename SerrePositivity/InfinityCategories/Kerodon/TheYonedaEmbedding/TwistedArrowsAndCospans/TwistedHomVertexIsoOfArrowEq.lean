module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomVertexEdgeClasses
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.CosliceTwistedHomVertexEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.CosliceTwistedHomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceFiberHomClass

/-!
概要：同じHom空間の元の二点の矢印の類の一致を、元の二点の同型へ戻す。
方針：元のcoslice比較の同じ逆と単位三角形を通して既存のcosliceの判定を使う。
規約：元の二点と両端を保持し、頂点同型を新たな前提にはしない。
使われ方：IS-W2 R03i、同じnative単位点の照合。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の矢印のArrowの類の等式から、同じ両端固定のHom空間の元の二点を結ぶ同型が存在する。 -/
lemma nonempty_twistedArrowHomSpace_vertexIso_of_arrow_eq {C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} {v w : (twistedArrowHomSpace x y) _⦋0⦌}
    (h : Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v.val)) =
      Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge w.val))) :
    Nonempty (VertexIso v w) := by
  let c := (cosliceTwistedHomMap_isQCatEquivalence x y).choose
  let v₀ := c.inv.app (Opposite.op ⦋0⦌) v
  let w₀ := c.inv.app (Opposite.op ⦋0⦌) w
  let ev : VertexIso (c.hom.app (Opposite.op ⦋0⦌) v₀) v := c.invHomIso.app v
  let ew : VertexIso (c.hom.app (Opposite.op ⦋0⦌) w₀) w := c.invHomIso.app w
  have hv := cosliceTwistedHomMap_vertex_edge_arrow v₀
  have hw := cosliceTwistedHomMap_vertex_edge_arrow w₀
  have hcos := hv.symm.trans ((twistedArrowHomSpace_vertexIso_arrow_eq ev).trans
    (h.trans ((twistedArrowHomSpace_vertexIso_arrow_eq ew).symm.trans hw)))
  have hp : cosliceFiberPointHom v₀ = cosliceFiberPointHom w₀ :=
    (Arrow.mk_inj _ _).mp hcos
  let e₀ := cosliceFiberVertexIsoOfHomEq hp
  exact ⟨ev.symm ≪≫ e₀.map c.hom ≪≫ ew⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

end
