module
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnderlyingSpaceInfinity
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.SourcePointedFiber
public import SerrePositivity.InfinityCategories.Derived.DGFiberTransportSquare
public import SerrePositivity.InfinityCategories.F1.Coherent.KanInvertible
/-!
概要：同じ基礎空間関手を普遍 pointed-space 射影へ表示し、元の実輸送で辺作用を判定する。
方針：同じ Yoneda 評価の始点固定 Tw 表示と両 fiber の実同値を用いる。
規約：点ごとの空間同値から関手比較の可逆性を先取りしない。
使われ方：実 augmentation を基礎空間へ送った辺の可逆性の証明。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v)
/-- 同じ基礎空間関手は、同じ実 Yoneda 関手を R の頂点で評価したもの。 -/
lemma dgHomUnderlyingSpaceInfinity_eq_yonedaEvaluation :
    dgHomUnderlyingSpaceInfinity R D = yonedaInfinityMap (dgHomModuleNerve R D) ≫
      evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm (dgHomModuleUnitVertex R D))) := by
  rw [yonedaInfinityMap, curry_evaluateFunctorAt_vertex]
  rfl
/-- 始点固定の実 Tw 全空間から、同じ普遍 pointed-space 圏への表示。 -/
def dgHomUnderlyingSpacePointedDisplay :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (twistedArrowSource (dgHomModuleUnitVertex R D)) ⟶
        PointedSpaceInfinity.{max (u + 1) v} :=
  twistedArrowSourcePointedDisplay (dgHomModuleUnitVertex R D)
/-- 同じ pointed 表示は、元の同じ基礎空間関手を底に持つ。 -/
lemma dgHomUnderlyingSpacePointedDisplay_projection :
    dgHomUnderlyingSpacePointedDisplay R D ≫ pointedSpaceProjection =
      (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (twistedArrowSourceProjection (dgHomModuleUnitVertex R D)) ≫
          dgHomUnderlyingSpaceInfinity R D := by
  rw [dgHomUnderlyingSpacePointedDisplay, twistedArrowSourcePointedDisplay_projection,
    dgHomUnderlyingSpaceInfinity_eq_yonedaEvaluation]
lemma dgHomUnderlyingSpacePointedDisplay_fiber_isQCatEquivalence
    (y : (dgHomModuleNerve R D) _⦋0⦌) :
    IsQCatEquivalence (transportSquareFiberMap
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (twistedArrowSourceProjection (dgHomModuleUnitVertex R D))) pointedSpaceProjection
      (dgHomUnderlyingSpacePointedDisplay R D) (dgHomUnderlyingSpaceInfinity R D)
      (dgHomUnderlyingSpacePointedDisplay_projection R D) (ULift.up y)) := by
  have H (G : (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgHomModuleNerve R D) ⟶ SpaceInfinity.{max (u + 1) v})
      (hG : G = yonedaInfinityMap (dgHomModuleNerve R D) ≫
        evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm (dgHomModuleUnitVertex R D))))
      (h : dgHomUnderlyingSpacePointedDisplay R D ≫ pointedSpaceProjection =
        (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
          (twistedArrowSourceProjection (dgHomModuleUnitVertex R D)) ≫ G) :
      IsQCatEquivalence (transportSquareFiberMap
        ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
          (twistedArrowSourceProjection (dgHomModuleUnitVertex R D))) pointedSpaceProjection
        (dgHomUnderlyingSpacePointedDisplay R D) G h (ULift.up y)) := by
    subst G
    exact twistedArrowSourcePointedDisplayFiber_isQCatEquivalence (dgHomModuleUnitVertex R D) y
  exact H _ (dgHomUnderlyingSpaceInfinity_eq_yonedaEvaluation R D)
    (dgHomUnderlyingSpacePointedDisplay_projection R D)
/-- 元の始点固定 Tw の実輸送が同値なら、同じ基礎空間関手で写した実辺は可逆。 -/
lemma dgHomUnderlyingSpaceInfinity_invertible_of_sourceTransport
    {y z : (dgHomModuleNerve R D) _⦋0⦌}
    (e : SSet.Edge (X := (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgHomModuleNerve R D)) (ULift.up y) (ULift.up z))
    (he : IsQCatEquivalence (edgeTransport
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (twistedArrowSourceProjection (dgHomModuleUnitVertex R D))) e)) :
    IsInvertibleEdge (e.map (dgHomUnderlyingSpaceInfinity R D)) := by
  have ht := (dgLeftFibrationSquareTransport_isQCatEquivalence_iff
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (twistedArrowSourceProjection (dgHomModuleUnitVertex R D))) pointedSpaceProjection
    (dgHomUnderlyingSpacePointedDisplay R D) (dgHomUnderlyingSpaceInfinity R D)
    (dgHomUnderlyingSpacePointedDisplay_projection R D) e
    (dgHomUnderlyingSpacePointedDisplay_fiber_isQCatEquivalence R D y)
    (dgHomUnderlyingSpacePointedDisplay_fiber_isQCatEquivalence R D z)).mp he
  exact pointedSpaceEdge_isInvertible_of_transport_isQCatEquivalence
    (e.map (dgHomUnderlyingSpaceInfinity R D)) ht
end SerrePositivity.InfinityCategories
