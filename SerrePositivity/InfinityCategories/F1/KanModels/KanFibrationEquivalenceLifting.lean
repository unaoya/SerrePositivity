module

public import SerrePositivity.InfinityCategories.HomotopyLimits.KanRelativePathLifting
public import SerrePositivity.InfinityCategories.F1B.Fibrations.IsofibrationCriterion
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLifting

/-!
概要：Kan fibration の元のホーン充填から同値持ち上げを得て、宇宙移送にも適用する。
方針：既存の相対 path 境界充填と isofibration 判定を使う。
規約：モデル構造の存在を追加仮定に置かない。
使われ方：元の局所 Hom の core の制限から pullback 比較への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

/-- Kan 複体間の Kan fibration は、同じ射で同値の相対持ち上げを持つ。 -/
lemma kanEquivalenceLifting_of_kanFibration {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p] :
    SerrePositivity.InfinityCategories.F1B.EquivalenceLifting p := by
  have hp := (SSet.modelCategoryQuillen.fibration_iff p).1 inferInstance
  have : InnerFibration p :=
    ⟨fun _ _ i hi ↦ hp i (innerHornInclusions_le_J i hi)⟩
  have : TrivialKanFibration (relativeEquivalencePathMapAt p 1) :=
    HomotopyLimits.relativeEquivalencePathMapAt_trivialKanFibration_of_fibration p 1
  intro T U j hj he
  exact SerrePositivity.InfinityCategories.F1B.equivalenceLifting_of_innerFibration_of_targetLifting p
    (SerrePositivity.InfinityCategories.F1B.invertibleTargetLifting_of_relativePath p) j hj he

/-- 同じ Kan fibration の宇宙持ち上げも、全ホーンを持ち上げる。 -/
lemma fibration_uliftFunctor_map {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    Fibration ((SSet.uliftFunctor.{v, u}).map p) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).2
  exact (SimplicialModel.UniverseLift.horn_rightClass_iff p).2
    ((SSet.modelCategoryQuillen.fibration_iff p).1 inferInstance)

/-- Kan fibration と交差する厳密 pullback は、元の他方の Kan 性を保つ。 -/
lemma kanComplex_pullback_of_fibration {A B D : SSet.{u}} [KanComplex D]
    (f : A ⟶ B) (g : D ⟶ B) [Fibration f] : KanComplex (pullback f g) := by
  have : Fibration (pullback.snd f g) := by
    apply (SSet.modelCategoryQuillen.fibration_iff _).2
    exact J.rlp.pullback_snd f g ((SSet.modelCategoryQuillen.fibration_iff f).1 inferInstance)
  exact isFibrant_of_fibration (pullback.snd f g)

end SerrePositivity.InfinityCategories
