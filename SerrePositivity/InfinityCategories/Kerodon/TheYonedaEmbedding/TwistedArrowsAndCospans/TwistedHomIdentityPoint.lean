module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.IdentityCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowVertexEdgeNerve

/-!
概要：元の始点固定の恒等点を同じ両端固定のHom空間へ制限する。
方針：元のfiber同型の包含則と元の恒等点の定値の式を適用する。
規約：元のtwistedArrowSourceIdentityそのものを使い、恒等点を選び直さない。
使われ方：元のnative単位点との同じHom空間での比較。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 元の始点固定の恒等点を、元のfiber同型で同じ両端固定のHom空間へ移す。 -/
def twistedArrowHomSpaceIdentityPoint {C : SSet.{u}} (x : C _⦋0⦌) :
    (twistedArrowHomSpace x x) _⦋0⦌ :=
  (twistedArrowSourceFiberIso x x).hom.app (Opposite.op ⦋0⦌)
    ⟨twistedArrowSourceIdentity x,
      (twistedArrowSourceIdentity_projection x).trans (pinchedConstant_zero x).symm⟩

/-- 元の恒等点の同じ像は、全空間で元の定値の重みの射になる。 -/
lemma twistedArrowHomSpaceIdentityPoint_value {C : SSet.{u}} (x : C _⦋0⦌) :
    (twistedArrowHomSpaceIdentityPoint x).val = SSet.const x := by
  let v : (vertexFiber (twistedArrowSourceProjection x) x) _⦋0⦌ :=
    ⟨twistedArrowSourceIdentity x,
      (twistedArrowSourceIdentity_projection x).trans (pinchedConstant_zero x).symm⟩
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌) v)
    (twistedArrowSourceFiberIso_ι x x)
  change (twistedArrowHomSpaceIdentityPoint x).val =
    (pullback.fst (twistedArrowProjection C) (twistedArrowSourceInclusion x)).app
      (Opposite.op ⦋0⦌) (twistedArrowSourceIdentity x) at h
  exact h.trans (twistedArrowSourceIdentity_fst x)

/-- 元の定値の重みの射から取り出した辺の類は、同じ頂点の恒等射。 -/
lemma twistedArrowVertexEdge_const_arrow {C : SSet.{u}} (x : C _⦋0⦌) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge (SSet.const x))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk x)) := by
  rw [← HomotopyCategory.homMk_id x]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  change yonedaEquiv ((edgewiseWeightIso 0).inv ≫ SSet.const x) = (SSet.Edge.id x).edge
  rw [SSet.comp_const]
  exact pinchedConstant_one x

/-- 元の同じ恒等点から取り出した辺の類は、同じ頂点の恒等射。 -/
lemma twistedArrowHomSpaceIdentityPoint_arrow {C : SSet.{u}} (x : C _⦋0⦌) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge (twistedArrowHomSpaceIdentityPoint x).val)) =
      Arrow.mk (𝟙 (HomotopyCategory.mk x)) := by
  have h := congrArg (fun v : (TwistedArrow C) _⦋0⦌ =>
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v)))
      (twistedArrowHomSpaceIdentityPoint_value x)
  exact h.trans (twistedArrowVertexEdge_const_arrow x)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

end
