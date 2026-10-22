module

public import SerrePositivity.InfinityCategories.HomotopyLimits.TwistedArrowPointedEdgeCospan
public import SerrePositivity.InfinityCategories.HomotopyLimits.TwistedArrowEdgeLifts

/-!
概要：二つの元の pointed 辺の底は、元の Yoneda 評価辺と反変辺そのもの。
方針：同じ全体の復元射の射影式を、元の二つの一単体に適用する。
規約：元の全辺の作用を厳密に照合し、Hom 類だけの一致へ弱めない。
使われ方：元の二方向の恒等点輸送を、同じ pointed 終点へ比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 始点側の元の pointed 辺の底は、元の Yoneda 射を始点で評価した同じ辺。 -/
lemma twistedArrowPointedSourceEdge_projection {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    pointedSpaceProjection.app (Opposite.op ⦋1⦌) (twistedArrowPointedSourceEdge f).edge =
      (yonedaInfinityMap C ≫ evaluateFunctorAt
        (ULift.up (SSet.opObjEquiv.symm
          (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))))).app
            (Opposite.op ⦋1⦌) (ULift.up (SSet.yonedaEquiv f)) := by
  rw [twistedArrowPointedSourceEdge_edge, yonedaInfinityMap_evaluate_sourceRestriction]
  have hp : (twistedArrowProjection C).app (Opposite.op ⦋1⦌)
      (twistedArrowSourceEdgeSimplex f) =
    (twistedArrowSourceInclusion
      (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))).app
        (Opposite.op ⦋1⦌) (SSet.yonedaEquiv f) := by
    have h := congrArg (fun g ↦ SSet.yonedaEquiv g) (twistedArrowSourceEdge_projection f)
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h
  have h := congrArg (fun g ↦ g.app (Opposite.op ⦋1⦌)
    (ULift.up (twistedArrowSourceEdgeSimplex f))) (twistedArrowPointedDisplay_projection C)
  change pointedSpaceProjection.app _
      ((twistedArrowPointedDisplay C).app _ (ULift.up (twistedArrowSourceEdgeSimplex f))) =
    (twistedArrowHomInfinity C).app _
      (ULift.up ((twistedArrowProjection C).app _ (twistedArrowSourceEdgeSimplex f))) at h
  rw [hp] at h
  exact h

/-- 終点側の元の pointed 辺の底は、同じ表現可能前層に元の反転辺を入れた辺。 -/
lemma twistedArrowPointedTargetEdge_projection {C : SSet.{u}} [Quasicategory C]
    (f : (Δ[1] : SSet.{u}) ⟶ C) :
    pointedSpaceProjection.app (Opposite.op ⦋1⦌) (twistedArrowPointedTargetEdge f).edge =
      (representablePresheafInfinity
        (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))).app (Opposite.op ⦋1⦌)
          (ULift.up (SSet.opObjEquiv.symm (SSet.yonedaEquiv f))) := by
  rw [twistedArrowPointedTargetEdge_edge, representablePresheafInfinity_eq_targetRestriction]
  have hp : (twistedArrowProjection C).app (Opposite.op ⦋1⦌)
      (twistedArrowTargetEdgeSimplex f) =
    (twistedArrowTargetInclusion
      (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1))).app
        (Opposite.op ⦋1⦌) (SSet.opObjEquiv.symm (SSet.yonedaEquiv f)) := by
    have h := congrArg (fun g ↦ SSet.yonedaEquiv g) (twistedArrowTargetEdge_projection f)
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, twistedArrowOppositeEdge]
      using h
  have h := congrArg (fun g ↦ g.app (Opposite.op ⦋1⦌)
    (ULift.up (twistedArrowTargetEdgeSimplex f))) (twistedArrowPointedDisplay_projection C)
  change pointedSpaceProjection.app _
      ((twistedArrowPointedDisplay C).app _ (ULift.up (twistedArrowTargetEdgeSimplex f))) =
    (twistedArrowHomInfinity C).app _
      (ULift.up ((twistedArrowProjection C).app _ (twistedArrowTargetEdgeSimplex f))) at h
  rw [hp] at h
  exact h

end SerrePositivity.InfinityCategories.HomotopyLimits
