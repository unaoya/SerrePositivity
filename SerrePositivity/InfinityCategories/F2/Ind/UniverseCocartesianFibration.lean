module

public import SerrePositivity.InfinityCategories.F2.Ind.UniverseCocartesianHornLifting
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianHornFibrationComparison

/-!
概要：元の cocartesian fibration の宇宙持ち上げは、追加仮定なしに cocartesian fibration。
方針：型付き基底辺を戻し、元の始点指定の持ち上げと外側ホーン充填を移送する。
規約：異なる界面の循環する instance は追加しない。使われ方：同じ weighted 射影上の全相対 join 図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の始点指定の cocartesian 輸送の宇宙持ち上げ。 -/
lemma cocartesianHornFibration_ulift {E B : SSet.{u}} (p : E ⟶ B)
    [CocartesianHornFibration p] :
    CocartesianHornFibration ((SSet.uliftFunctor.{v, u}).map p) where
  mem := InnerFibration.mem
  exists_lift x b a := by
    obtain ⟨x⟩ := x
    obtain ⟨b⟩ := b
    let a₀ : SSet.Truncated.Edge (X := (truncation 2).obj B)
        (p.app (Opposite.op ⦋0⦌) x) b :=
      { edge := a.edge.down
        src_eq := congrArg ULift.down a.src_eq
        tgt_eq := congrArg ULift.down a.tgt_eq }
    obtain ⟨y, e, he, hc⟩ := CocartesianHornFibration.exists_lift (p := p) x b a₀
    refine ⟨ULift.up y, uliftTruncatedEdge.{u, v} e, ?_, hasCocartesianHornLifting_ulift p e hc⟩
    change ULift.up (p.app (Opposite.op ⦋1⦌) e.edge) = a.edge
    apply ULift.ext
    exact he

/-- 元の cocartesian fibration の同じ射を宇宙持ち上げした射も cocartesian fibration。 -/
lemma cocartesianFibration_ulift {E B : SSet.{u}} (p : E ⟶ B) [CocartesianFibration p] :
    CocartesianFibration ((SSet.uliftFunctor.{v, u}).map p) := by
  have : CocartesianHornFibration p := CocartesianFibration.toCocartesianHornFibration p
  have : CocartesianHornFibration ((SSet.uliftFunctor.{v, u}).map p) :=
    cocartesianHornFibration_ulift p
  exact F1B.kanCocartesianHornFibration_toCocartesianFibration _

end SerrePositivity.InfinityCategories.F2.Ind
