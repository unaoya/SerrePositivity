module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackInputFibration
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanFibrationHomotopyLift

/-!
概要：path 引き戻しの二入力の指定輸送を、指定全 path とともに持ち上げる。
方針：二入力射の Kan fibration 性で二円柱の組を始点固定で持ち上げる。
規約：元の引き戻し射を始点にし、二入力の全輸送円柱を厳密に保持する。
使われ方：有限標的射の二入力を元の全空間への射で表す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：二入力の指定ホモトピーを元の path 引き戻し内のホモトピーへ持ち上げる。
方針：二入力射へ組の円柱を持ち上げ、終端の二座標を読む。
規約：指定した二つの全円柱を保持。使われ方：元の二入力による有限標的射の表示。 -/
lemma intervalPullback_transport_inputs {K E D H : SSet.{u}} [KanComplex H]
    (f : E ⟶ H) (g : D ⟶ H) (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback f g) (u : K ⟶ E) (v : K ⟶ D)
    (U : SSet.Homotopy (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft f g) u)
    (V : SSet.Homotopy (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight f g) v) :
    ∃ e : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback f g, e ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft f g = u ∧
      e ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight f g = v ∧ ∃ L : SSet.Homotopy a e,
        L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackInputPair f g = lift U.h V.h := by
  let H : SSet.Homotopy (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackInputPair f g) (lift u v) :=
    { h := lift U.h V.h
      h₀ := by
        change SSet.ι₀ ≫ lift U.h V.h = a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackInputPair f g
        rw [comp_lift, U.h₀, V.h₀]
        rfl
      h₁ := by
        change SSet.ι₁ ≫ lift U.h V.h = lift u v
        rw [comp_lift, U.h₁, V.h₁]
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  obtain ⟨e, L, hL⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanFibration_lift_homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackInputPair f g) a H
  have he : e ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackInputPair f g = lift u v := by
    have h := congrArg (fun r ↦ SSet.ι₁ ≫ r) hL
    rw [← Category.assoc, L.h₁, H.h₁] at h
    exact h
  refine ⟨e, ?_, ?_, L, hL⟩
  · have h := congrArg (fun r ↦ r ≫ fst E D) he
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackInputPair, Category.assoc, lift_fst] using h
  · have h := congrArg (fun r ↦ r ≫ snd E D) he
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackInputPair, Category.assoc, lift_snd] using h

end SerrePositivity.InfinityCategories.Project.FilteredExchange
