module

public import SerrePositivity.InfinityCategories.F1.RelativeHomIdentityCoefficient
public import SerrePositivity.InfinityCategories.F1.RelativeHomCosliceKanAction
public import SerrePositivity.InfinityCategories.F1.PointFunctorEvaluation

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
namespace SerrePositivity.InfinityCategories

/-- 相対恒等射の一点 Hom 係数に、全反転 Hom の実際の豊穣評価を作用させる。 -/
def relativeHomIdentityAction {B : SSet.{u}} (q r : LeftFibrationObject B) :
    ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom q r)).op ⟶
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject
        ((relativeFunctorEnrichedEvaluation q.val).obj r))).op :=
  lift (SSet.const (relativeHomIdentityCoefficient q))
    (SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
      ((relativeFunctorEnrichedEvaluation q.val).map q r))) ≫
    coherentReverseHomComposition
      (Opposite.op ((relativeFunctorEnrichedEvaluation q.val).obj r))
      (Opposite.op ((relativeFunctorEnrichedEvaluation q.val).obj q))
      (Opposite.op pointKanObject)

/-- 実際の大域比較は、全反転 Hom 上で同じ恒等射係数の合成作用を表す。 -/
def relativeHomCosliceComparisonFiber_identityActionIso {B : SSet.{u}}
    (q r : LeftFibrationObject B) :
    FunctorIso
      (((HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom q r)).inv ≫
        HomotopyLimits.coherentCosliceFiberComparison q r) ≫
          relativeHomCosliceComparisonFiber q r)
      (relativeHomIdentityAction q r ≫
        pointedReverseKanFiberComparison ((relativeFunctorEnrichedEvaluation q.val).obj r)) := by
  have e := pointedReverseKanCompositionTransport_diagonalIso
    ((relativeFunctorEnrichedEvaluation q.val).obj q)
    ((relativeFunctorEnrichedEvaluation q.val).obj r)
    (SSet.const (relativeHomIdentityCoefficient q))
    (SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
      ((relativeFunctorEnrichedEvaluation q.val).map q r)))
  have hid : (SSet.const (relativeHomIdentityCoefficient q) :
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom q r)).op ⟶ _) ≫
      pointedReverseKanFiberComparison ((relativeFunctorEnrichedEvaluation q.val).obj q) =
      SSet.const (relativeHomPointedIdentity q) :=
    relativeHomIdentityCoefficient_family q _
  rw [hid] at e
  exact relativeHomCosliceComparisonFiber_enrichedActionIso q r ≪≫ e.symm

/-- 恒等射への作用は、同じ Hom の点を一点 Hom に移す標準の同型そのもの。 -/
lemma relativeHomIdentityAction_eq {B : SSet.{u}} (q r : LeftFibrationObject B) :
    relativeHomIdentityAction q r = SSet.opFunctor.map
      ((SSet.uliftFunctor.{u + 1, u}).map
        (pointFunctorEvaluationIso ((relativeFunctorEnrichedEvaluation q.val).obj r).obj).inv) := by
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

end SerrePositivity.InfinityCategories
