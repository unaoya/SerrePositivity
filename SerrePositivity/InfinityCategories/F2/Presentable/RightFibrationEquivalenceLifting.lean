module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1B.Diagrams.OppositeLifting
public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalOppositeFibration

/-!
概要：right fibration の同値持ち上げ性を反転から回収する。
方針：元の射を反転して left fibration の公開判定を適用し、二重反転を戻す。
規約：モデル構造の仮定を要求しない。
使われ方：compact 始域 slice の射影に沿う小模型同値の底変換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：right fibration は単射な前合成同値を右に持ち上げる。
方針：left fibration の判定と同値持ち上げ性の反転保存を合成する。
規約：始域と標的は quasicategory。
使われ方：元の slice 射影に沿う同値の厳密な引き戻し。 -/
lemma rightFibration_equivalenceLifting {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [RightFibration p] :
    F1B.EquivalenceLifting p := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  intro A B i hm hi
  have : Mono i := hm
  have h := leftFibration_equivalenceLifting (SSet.opFunctor.map p)
    (SSet.opFunctor.map i) inferInstance (F1B.isPrecompositionEquivalence_op hi)
  exact (SSet.opFunctor.hasLiftingProperty_iff_of_isEquivalence i p).mp h


end SerrePositivity.InfinityCategories.F2.Presentable
