module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CommutingArrowSquare
public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteConeEdgeReconstruction

/-!
概要：元の二つの離散全錐の全脚の可換式を、矢印関手圏内の実際の全錐にまとめる。
方針：各指定正方形を同じ頂点比較の間の辺とし、元の離散辺族から全錐を構成する。
規約：元の頂点比較・各成分比較・全脚の一単体を保持する。有限性は不要。
使われ方：全錐の関手同型と極限性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory
variable {J : Type u} {X : SSet.{u + 1}} [Quasicategory X]
  {p q : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶ X}
  (c : JoinCone p) (d : JoinCone q) (e : SSet.Edge c.vertex d.vertex)
  (f : (j : J) → SSet.Edge
    (p.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk j))))
    (q.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk j)))))
  (h : ∀ j, homMk e.toTruncated ≫
    homMk (F2.nativeConeLeg d (ULift.up (nerveVertex (Discrete.mk j)))) =
    homMk (F2.nativeConeLeg c (ULift.up (nerveVertex (Discrete.mk j)))) ≫
      homMk (f j).toTruncated)

/-- 元の各成分比較辺を頂点とする、同じ離散形状の矢印関手図式。 -/
def discreteConeArrowDiagram :=
  liftedDiscreteVertexMap (fun j => functorVertex (SSet.yonedaEquiv.symm (f j).edge))

include h in
/-- 同じ指定正方形を、同じ頂点比較から元の成分比較へ向かう実際の辺として保持。 -/
def discreteConeArrowLeg (j : J) :
    SSet.Edge (X := (ihom (Δ[1] : SSet.{u + 1})).obj X)
      (functorVertex (SSet.yonedaEquiv.symm e.edge))
      ((discreteConeArrowDiagram f).app (Opposite.op ⦋0⦌)
        (ULift.up (nerveVertex (Discrete.mk j)))) :=
  (commutingArrowSquareEdge e (f j)
    (SSet.Edge.ofTruncated (F2.nativeConeLeg c (ULift.up (nerveVertex (Discrete.mk j)))))
    (SSet.Edge.ofTruncated (F2.nativeConeLeg d (ULift.up (nerveVertex (Discrete.mk j)))))
    (h j)).ofEq rfl (liftedDiscreteVertexMap_vertex
      (fun j => functorVertex (SSet.yonedaEquiv.symm (f j).edge)) j).symm

include h in
/-- 元の全脚の可換式をまとめた、矢印関手圏内の同じ離散全錐。 -/
def discreteConeArrowCone : JoinCone (discreteConeArrowDiagram f) :=
  discreteConeFromEdges (discreteConeArrowDiagram f)
    (fun j => (discreteConeArrowLeg c d e f h j).toTruncated)

/-- 同じ矢印全錐の頂点は、元の指定された一つの頂点比較辺。 -/
lemma discreteConeArrowCone_vertex :
    (discreteConeArrowCone c d e f h).vertex =
      functorVertex (SSet.yonedaEquiv.symm e.edge) :=
  discreteConeFromEdges_vertex _ _

/-- 元の全錐の各脚を始点で評価すると、元の同じ c の脚の全一単体。 -/
lemma discreteConeArrowCone_leg_zero (j : J) :
    (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋1⦌)
      (F2.nativeConeLeg (discreteConeArrowCone c d e f h)
        (ULift.up (nerveVertex (Discrete.mk j)))).edge =
    (F2.nativeConeLeg c (ULift.up (nerveVertex (Discrete.mk j)))).edge := by
  have H := congrArg (fun a =>
    (evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
      (Opposite.op ⦋1⦌) a) (discreteConeFromEdges_leg_edge (discreteConeArrowDiagram f)
        (fun j => (discreteConeArrowLeg c d e f h j).toTruncated) j)
  exact H.trans (commutingArrowSquareEdge_zero e (f j) _ _ (h j))

/-- 元の全錐の各脚を終点で評価すると、元の同じ d の脚の全一単体。 -/
lemma discreteConeArrowCone_leg_one (j : J) :
    (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋1⦌)
      (F2.nativeConeLeg (discreteConeArrowCone c d e f h)
        (ULift.up (nerveVertex (Discrete.mk j)))).edge =
    (F2.nativeConeLeg d (ULift.up (nerveVertex (Discrete.mk j)))).edge := by
  have H := congrArg (fun a =>
    (evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
      (Opposite.op ⦋1⦌) a) (discreteConeFromEdges_leg_edge (discreteConeArrowDiagram f)
        (fun j => (discreteConeArrowLeg c d e f h j).toTruncated) j)
  exact H.trans (commutingArrowSquareEdge_one e (f j) _ _ (h j))

end SerrePositivity.InfinityCategories.HomotopyLimits
