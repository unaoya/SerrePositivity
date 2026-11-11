module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomIdentityCoefficient
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomCosliceKanAction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：実際の Hom 大域比較を、恒等射係数に作用する反転した豊穣合成へ移す。
方針：同じ pointed 恒等点の係数表示を合成輸送の対角比較に代入する。
規約：元の反転 Hom 全体と元の大域比較の fiber 射を使用する。
使われ方：合成の単位則から実際の fiber 比較の同値性へ進む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 相対恒等射の一点 Hom 係数に、全反転 Hom の実際の豊穣評価を作用させる。 -/
def relativeHomIdentityAction {B : SSet.{u}} (q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom q r)).op ⟶
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val).obj r))).op :=
  lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityCoefficient q))
    (SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val).map q r))) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentReverseHomComposition
      (Opposite.op ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val).obj r))
      (Opposite.op ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val).obj q))
      (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject)

/-- 実際の大域比較は、全反転 Hom 上で同じ恒等射係数の合成作用を表す。 -/
def relativeHomCosliceComparisonFiber_identityActionIso {B : SSet.{u}}
    (q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom q r)).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentCosliceFiberComparison q r) ≫
          _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCosliceComparisonFiber q r)
      (relativeHomIdentityAction q r ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedReverseKanFiberComparison ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val).obj r)) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedReverseKanCompositionTransport_diagonalIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val).obj q)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val).obj r)
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityCoefficient q))
    (SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val).map q r)))
  have hid : (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityCoefficient q) :
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom q r)).op ⟶ _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedReverseKanFiberComparison ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val).obj q) =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomPointedIdentity q) :=
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomIdentityCoefficient_family q _
  rw [hid] at e
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCosliceComparisonFiber_enrichedActionIso q r ≪≫ e.symm

/-- 恒等射への作用は、同じ Hom の点を一点 Hom に移す標準の同型そのもの。 -/
lemma relativeHomIdentityAction_eq {B : SSet.{u}} (q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    relativeHomIdentityAction q r = SSet.opFunctor.map
      ((SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val).obj r).obj).inv) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply SSet.opObjEquiv.injective
  apply ULift.ext
  apply Functor.HomObj.ext
  funext m α
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  apply Functor.HomObj.ext
  funext k β
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
