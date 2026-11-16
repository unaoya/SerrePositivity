module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningAllBasesEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation

/-!
概要：元の全評価同型の成分を、元の図式の値と同じ実fiberの頂点へ合わせる。
方針：元の図式の頂点の等式と同じcoherentなfiber評価の頂点の等式を合成する。
規約：元の指定評価同型を使い、新しい同値を選ばない。
使われ方：同じ全変換を実際のfiber射へ厳密に照合する。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の図式の同じ点の値は、元の全分類と同じ評価の合成の同じ点の値。 -/
lemma leftStraighteningInfinityDiagram_fiber_vertex {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    (leftStraighteningInfinityDiagram p).app (Opposite.op ⦋0⦌) (ULift.up b) =
      (leftStraighteningInfinityMap B ≫ evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b)).app
        (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p) := by
  have hp := evaluateFunctorAt_functorVertex (ULift.up b) (leftStraighteningInfinityDiagram p)
  have hv := congrArg
    ((evaluateFunctorAt (X := (SSet.uliftFunctor.{u+1,u}).obj B)
      (Y := SpaceInfinity.{u}) (ULift.up b)).app (Opposite.op ⦋0⦌))
    (leftStraighteningInfinityDiagram_vertex p)
  exact hp.symm.trans hv

/-- 元の全評価同型の同じ成分を、元の図式の値と実際のfiberの標準頂点へ等式だけで移す。 -/
def leftStraighteningInfinityDiagram_fiberIso {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    VertexIso ((leftStraighteningInfinityDiagram p).app (Opposite.op ⦋0⦌) (ULift.up b))
      (coherentNerveVertex (leftFibrationFiberObject b (leftFibrationObjectOf p))) :=
  eqToIso (congrArg HomotopyCategory.mk (leftStraighteningInfinityDiagram_fiber_vertex p b)) ≪≫
    (leftStraighteningInfinityMap_evaluateIso b).app (leftFibrationInfinityVertex p) ≪≫
      eqToIso (congrArg HomotopyCategory.mk (leftFibrationInfinityFiberEvaluation_vertex b
        (leftFibrationObjectOf p)))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

end
