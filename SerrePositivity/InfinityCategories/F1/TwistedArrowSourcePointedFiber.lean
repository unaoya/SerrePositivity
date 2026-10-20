module

public import SerrePositivity.InfinityCategories.F1.TwistedArrowPointedIdentity

/-!
概要：始点固定の実際の pointed 比較の fiber 作用は、全ての終点で同値。
方針：持ち上げた pullback fiber の厳密な同型に、全体の pointed 比較の fiber 同値を続ける。
規約：底は同じ Yoneda 写像の指定点評価で、端点の等式を明示する。
使われ方：正方形の輸送自然性に終点の fiber 同値を渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 始点固定の持ち上げた fiber を、全体の両端固定の持ち上げた fiber へ厳密に移す。 -/
def twistedArrowSourceLiftedFiberIso {C : SSet.{u}} (x y : C _⦋0⦌) :
    vertexFiber ((SSet.uliftFunctor.{u + 1, u}).map (twistedArrowSourceProjection x)) (ULift.up y) ≅
    vertexFiber ((SSet.uliftFunctor.{u + 1, u}).map (twistedArrowProjection C))
      (ULift.up (SSet.opObjEquiv.symm x, y)) :=
  (uliftVertexFiberIso.{u, u + 1} (twistedArrowSourceProjection x) y).symm ≪≫
    (SSet.uliftFunctor.{u + 1, u}).mapIso (twistedArrowSourceFiberIso x y) ≪≫
    uliftVertexFiberIso.{u, u + 1} (twistedArrowProjection C) (SSet.opObjEquiv.symm x, y)

/-- 同じ同型は、元の持ち上げた全空間への包含を厳密に保つ。 -/
lemma twistedArrowSourceLiftedFiberIso_ι {C : SSet.{u}} (x y : C _⦋0⦌) :
    (twistedArrowSourceLiftedFiberIso x y).hom ≫
      vertexFiberι ((SSet.uliftFunctor.{u + 1, u}).map (twistedArrowProjection C))
        (ULift.up (SSet.opObjEquiv.symm x, y)) =
    vertexFiberι ((SSet.uliftFunctor.{u + 1, u}).map (twistedArrowSourceProjection x))
      (ULift.up y) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (pullback.fst (twistedArrowProjection C) (twistedArrowSourceInclusion x)) := by
  dsimp only [twistedArrowSourceLiftedFiberIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [uliftVertexFiberIso_hom_ι, ← Functor.map_comp,
    twistedArrowSourceFiberIso_ι, Functor.map_comp]
  have h := congrArg (fun f ↦ f ≫ (SSet.uliftFunctor.{u + 1, u}).map
    (pullback.fst (twistedArrowProjection C) (twistedArrowSourceInclusion x)))
    (uliftVertexFiberIso_inv_ι.{u, u + 1} (twistedArrowSourceProjection x) y)
  simpa only [Category.assoc] using h

/-- 始点固定の底の指定頂点での値は、元の両端固定の Hom 図式の同じ値。 -/
lemma twistedArrowSourcePointedDisplay_vertex {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) :
    (yonedaInfinityMap C ≫ evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x))).app
      (Opposite.op ⦋0⦌) (ULift.up y) =
    (twistedArrowHomInfinity C).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm x, y)) := by
  rw [yonedaInfinityMap_evaluate_sourceRestriction]
  change (twistedArrowHomInfinity C).app _
    (ULift.up ((twistedArrowSourceInclusion x).app _ y)) = _
  rw [twistedArrowSourceInclusion_vertex]

/-- 始点固定の同じ pointed 比較が誘導する、元の底を保つ実際の fiber 射。 -/
def twistedArrowSourcePointedDisplayFiber {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :=
  transportSquareFiberMap ((SSet.uliftFunctor.{u + 1, u}).map (twistedArrowSourceProjection x))
    pointedSpaceProjection (twistedArrowSourcePointedDisplay x)
    (yonedaInfinityMap C ≫ evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x)))
    (twistedArrowSourcePointedDisplay_projection x) (ULift.up y)

/-- 始点固定の実際の fiber 射は、全体の fiber 同値を同じ同型と端点表示で移したもの。 -/
lemma twistedArrowSourcePointedDisplayFiber_compare {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) :
    twistedArrowSourcePointedDisplayFiber x y =
    (twistedArrowSourceLiftedFiberIso x y).hom ≫
      twistedArrowPointedDisplayFiber C (SSet.opObjEquiv.symm x, y) ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (twistedArrowSourcePointedDisplay_vertex x y).symm) := by
  apply vertexFiber_hom_ext pointedSpaceProjection
    ((yonedaInfinityMap C ≫ evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x))).app
      (Opposite.op ⦋0⦌) (ULift.up y))
  simp only [twistedArrowSourcePointedDisplayFiber, Category.assoc]
  rw [transportSquareFiberMap_ι, vertexFiberTransport_ι _
    (twistedArrowSourcePointedDisplay_vertex x y).symm]
  rw [twistedArrowPointedDisplayFiber, transportSquareFiberMap_ι,
    ← Category.assoc, twistedArrowSourceLiftedFiberIso_ι]
  rfl

/-- 同じ Yoneda 指定点評価を底に持つ、始点固定の実際の fiber 射は全ての終点で同値。 -/
lemma twistedArrowSourcePointedDisplayFiber_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    IsQCatEquivalence (twistedArrowSourcePointedDisplayFiber x y) := by
  rw [twistedArrowSourcePointedDisplayFiber_compare]
  have h₁ := (qCatEquivalenceOfIso (twistedArrowSourceLiftedFiberIso x y)).isQCatEquivalence
  have h₂ := twistedArrowPointedDisplayFiber_isQCatEquivalence C (SSet.opObjEquiv.symm x, y)
  have h₃ := (qCatEquivalenceOfIso (eqToIso (congrArg (vertexFiber pointedSpaceProjection)
    (twistedArrowSourcePointedDisplay_vertex x y).symm))).isQCatEquivalence
  exact h₁.comp (h₂.comp h₃)

end SerrePositivity.InfinityCategories
