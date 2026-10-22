module

public import SerrePositivity.InfinityCategories.F2.Ind.LiftedIntervalEndpoints
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramConePointUncurry

/-!
概要：正規化した元の射の終点 comma を、同じ元の評価頂点の comma へ戻す。
方針：区間の両端点の厳密な宇宙比較で固定図式を表示変更する。
規約：C 側の射影と全錐を保持。使われ方：元の終点 comma の円柱族 F。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)

/-- 正規化した終点の全点写像は、元の指定終点の点写像そのもの。 -/
lemma indArrowEndpoint_point : stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D) =
    SSet.yonedaEquiv.symm
      (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))) := by
  rw [← Category.assoc, liftedIntervalToSmall_last, diagramShapePoint,
    SSet.yonedaEquiv_symm_comp]

/-- 正規化した終点の comma と、元の同じ評価頂点の comma の厳密な同型。 -/
def indArrowEndpointCommaIso :
    pullback (indYoneda κ C)
      (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))) ≅
        leftKanShape (indYoneda κ C)
          (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))) :=
  eqToIso (congrArg (fun p => pullback (indYoneda κ C) (sliceOverProjection p))
    (indArrowEndpoint_point κ D))

/-- 表示変更でも元の C 側の全図式は厳密に保たれる。 -/
lemma indArrowEndpointCommaIso_projection : (indArrowEndpointCommaIso κ D).hom ≫
    leftKanProjection (indYoneda κ C)
      (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))) =
        pullback.fst (indYoneda κ C)
          (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))) :=
  slicePullbackTransport_projection (indYoneda κ C) (indArrowEndpoint_point κ D)

end SerrePositivity.InfinityCategories.F2.Ind
