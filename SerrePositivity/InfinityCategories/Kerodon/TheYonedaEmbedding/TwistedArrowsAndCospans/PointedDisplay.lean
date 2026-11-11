module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.IdentityCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CanonicalYonedaFiberTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseLeftFibration

/-!
概要：元の Tw 全体から普遍 pointed-space 射影への一つの比較と、その始点固定の制限。
方針：同じ全体の復元射・縮小同型・第一射影を合成し、curry の評価公式で底を照合する。
規約：始点固定の底は、同じ yonedaInfinityMap の指定点評価そのもの。
使われ方：Tw の恒等点からの輸送を c1 の実際の普遍輸送へ送る。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

local instance {C : SSet.{u}} [Quasicategory C] : Quasicategory (C.op ⊗ C) :=
  quasicategory_of_innerFibration (fst C.op C)

/-- 同じ全体の復元射から取る、元の Tw の持ち上げから pointed-space への比較。 -/
def twistedArrowPointedDisplay (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityReconstruction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C)).hom ≫
    pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C)

/-- 同じ pointed 比較の底は、元の両端射影に実際の分類図式を続けたもの。 -/
lemma twistedArrowPointedDisplay_projection (C : SSet.{u}) [Quasicategory C] :
    twistedArrowPointedDisplay C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C := by
  rw [twistedArrowPointedDisplay, Category.assoc, Category.assoc, pullback.condition]
  change (SSet.uliftFunctor.map _) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C) ≫ _ = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso _).hom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso_projection, ← Functor.map_comp_assoc]
  exact congrArg (fun f ↦ (SSet.uliftFunctor.{u + 1, u}).map f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityReconstruction_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C))

/-- 同じ Yoneda 写像を第一変数の頂点で評価すると、実際の Hom 図式の始点固定の制限。 -/
lemma yonedaInfinityMap_evaluate_sourceRestriction {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x)) =
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation, ← Category.assoc]
  congr 1

/-- 始点固定の元の Tw 全空間から、同じ全体の pointed 比較を制限する。 -/
def twistedArrowSourcePointedDisplay {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSource x) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion x)) ≫
    twistedArrowPointedDisplay C

/-- 同じ制限した全空間の射の底は、同じ Yoneda 写像の指定点での評価そのもの。 -/
lemma twistedArrowSourcePointedDisplay_projection {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) :
    twistedArrowSourcePointedDisplay x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection x) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x))) := by
  rw [twistedArrowSourcePointedDisplay, Category.assoc,
    twistedArrowPointedDisplay_projection, yonedaInfinityMap_evaluate_sourceRestriction]
  rw [← Functor.map_comp_assoc, pullback.condition, Functor.map_comp, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
