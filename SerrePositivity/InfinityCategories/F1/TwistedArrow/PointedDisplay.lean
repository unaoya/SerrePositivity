module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.IdentityCoordinates
public import SerrePositivity.InfinityCategories.F1.Yoneda.CanonicalYonedaFiberTransport
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftFibration

/-!
概要：元の Tw 全体から普遍 pointed-space 射影への一つの比較と、その始点固定の制限。
方針：同じ全体の復元射・縮小同型・第一射影を合成し、curry の評価公式で底を照合する。
規約：始点固定の底は、同じ yonedaInfinityMap の指定点評価そのもの。
使われ方：Tw の恒等点からの輸送を c1 の実際の普遍輸送へ送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {C : SSet.{u}} [Quasicategory C] : Quasicategory (C.op ⊗ C) :=
  quasicategory_of_innerFibration (fst C.op C)

/-- 同じ全体の復元射から取る、元の Tw の持ち上げから pointed-space への比較。 -/
def twistedArrowPointedDisplay (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (TwistedArrow C) ⟶ PointedSpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map
      (leftStraighteningInfinityReconstruction (twistedArrowProjection C)) ≫
    (smallLeftUnstraighteningIso (twistedArrowHomInfinity C)).hom ≫
    pullback.fst pointedSpaceProjection (twistedArrowHomInfinity C)

/-- 同じ pointed 比較の底は、元の両端射影に実際の分類図式を続けたもの。 -/
lemma twistedArrowPointedDisplay_projection (C : SSet.{u}) [Quasicategory C] :
    twistedArrowPointedDisplay C ≫ pointedSpaceProjection =
    (SSet.uliftFunctor.{u + 1, u}).map (twistedArrowProjection C) ≫
      twistedArrowHomInfinity C := by
  rw [twistedArrowPointedDisplay, Category.assoc, Category.assoc, pullback.condition]
  change (SSet.uliftFunctor.map _) ≫
    (smallLeftUnstraighteningIso (twistedArrowHomInfinity C)).hom ≫
      leftUnstraighteningProjection (twistedArrowHomInfinity C) ≫ _ = _
  rw [← Category.assoc (smallLeftUnstraighteningIso _).hom,
    smallLeftUnstraighteningIso_projection, ← Functor.map_comp_assoc]
  exact congrArg (fun f ↦ (SSet.uliftFunctor.{u + 1, u}).map f ≫ twistedArrowHomInfinity C)
    (leftStraighteningInfinityReconstruction_projection (twistedArrowProjection C))

/-- 同じ Yoneda 写像を第一変数の頂点で評価すると、実際の Hom 図式の始点固定の制限。 -/
lemma yonedaInfinityMap_evaluate_sourceRestriction {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) :
    yonedaInfinityMap C ≫ evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x)) =
    (SSet.uliftFunctor.{u + 1, u}).map (twistedArrowSourceInclusion x) ≫
      twistedArrowHomInfinity C := by
  rw [yonedaInfinityMap, curry_evaluateFunctorAt_vertex,
    homInfinityJointEvaluation, ← Category.assoc]
  congr 1

/-- 始点固定の元の Tw 全空間から、同じ全体の pointed 比較を制限する。 -/
def twistedArrowSourcePointedDisplay {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj (twistedArrowSource x) ⟶ PointedSpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map
      (pullback.fst (twistedArrowProjection C) (twistedArrowSourceInclusion x)) ≫
    twistedArrowPointedDisplay C

/-- 同じ制限した全空間の射の底は、同じ Yoneda 写像の指定点での評価そのもの。 -/
lemma twistedArrowSourcePointedDisplay_projection {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) :
    twistedArrowSourcePointedDisplay x ≫ pointedSpaceProjection =
    (SSet.uliftFunctor.{u + 1, u}).map (twistedArrowSourceProjection x) ≫
      (yonedaInfinityMap C ≫ evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x))) := by
  rw [twistedArrowSourcePointedDisplay, Category.assoc,
    twistedArrowPointedDisplay_projection, yonedaInfinityMap_evaluate_sourceRestriction]
  rw [← Functor.map_comp_assoc, pullback.condition, Functor.map_comp, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories
