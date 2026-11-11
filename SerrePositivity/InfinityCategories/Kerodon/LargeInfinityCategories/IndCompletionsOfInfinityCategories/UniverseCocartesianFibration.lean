module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.UniverseCocartesianHornLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibrationComparison

/-!
概要：元の cocartesian fibration の宇宙持ち上げは、追加仮定なしに cocartesian fibration。
方針：型付き基底辺を戻し、元の始点指定の持ち上げと外側ホーン充填を移送する。
規約：異なる界面の循環する instance は追加しない。使われ方：同じ weighted 射影上の全相対 join 図式。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の始点指定の cocartesian 輸送の宇宙持ち上げ。 -/
lemma cocartesianHornFibration_ulift {E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration ((SSet.uliftFunctor.{v, u}).map p) where
  mem := InnerFibration.mem
  exists_lift x b a := by
    obtain ⟨x⟩ := x
    obtain ⟨b⟩ := b
    let a₀ : SSet.Truncated.Edge (X := (truncation 2).obj B)
        (p.app (Opposite.op ⦋0⦌) x) b :=
      { edge := a.edge.down
        src_eq := congrArg ULift.down a.src_eq
        tgt_eq := congrArg ULift.down a.tgt_eq }
    obtain ⟨y, e, he, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration.exists_lift (p := p) x b a₀
    refine ⟨ULift.up y, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, v} e, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasCocartesianHornLifting_ulift p e hc⟩
    change ULift.up (p.app (Opposite.op ⦋1⦌) e.edge) = a.edge
    apply ULift.ext
    exact he

/-- 元の cocartesian fibration の同じ射を宇宙持ち上げした射も cocartesian fibration。 -/
lemma cocartesianFibration_ulift {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration ((SSet.uliftFunctor.{v, u}).map p) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration.toCocartesianHornFibration p
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration ((SSet.uliftFunctor.{v, u}).map p) :=
    cocartesianHornFibration_ulift p
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianHornFibration_toCocartesianFibration _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
