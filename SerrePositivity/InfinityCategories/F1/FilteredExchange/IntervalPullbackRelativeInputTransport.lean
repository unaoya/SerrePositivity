module

public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.IntervalPullbackInputFibration
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanFibrationRelativeHomotopyLift

/-!
概要：path 引き戻しの二入力を、指定した部分 path の全円柱を保って輸送する。
方針：二入力射の相対 Kan 持ち上げを使い、終点と指定部分円柱を読む。
規約：元の始点・二入力輸送・部分 path の輸送を同時に厳密に保持する。
使われ方：標的側の境界付き有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二入力の輸送は、指定部分円柱を保って引き戻し内へ持ち上がる。
方針：相対 Kan 持ち上げの底として二入力の円柱を組にする。
規約：全時刻の厳密な制限式。使われ方：境界を保つ元の二入力への変形。 -/
lemma intervalPullback_transport_inputs_relative {A K E D H : SSet.{u}} [KanComplex H]
    (f : E ⟶ H) (g : D ⟶ H) (i : A ⟶ K) [Mono i]
    (a : K ⟶ intervalPullback f g) (u : K ⟶ E) (v : K ⟶ D)
    (U : SSet.Homotopy (a ≫ intervalPullbackLeft f g) u)
    (V : SSet.Homotopy (a ≫ intervalPullbackRight f g) v)
    (a₀ : A ⟶ intervalPullback f g) (L : SSet.Homotopy (i ≫ a) a₀)
    (hU : (i ▷ (Δ[1] : SSet.{u})) ≫ U.h = L.h ≫ intervalPullbackLeft f g)
    (hV : (i ▷ (Δ[1] : SSet.{u})) ≫ V.h = L.h ≫ intervalPullbackRight f g) :
    ∃ e : K ⟶ intervalPullback f g, i ≫ e = a₀ ∧
      e ≫ intervalPullbackLeft f g = u ∧ e ≫ intervalPullbackRight f g = v ∧
      ∃ G : SSet.Homotopy a e, (i ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ∧
        G.h ≫ intervalPullbackInputPair f g = lift U.h V.h := by
  let H : SSet.Homotopy (a ≫ intervalPullbackInputPair f g) (lift u v) :=
    { h := lift U.h V.h
      h₀ := by
        change SSet.ι₀ ≫ lift U.h V.h = a ≫ intervalPullbackInputPair f g
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
  have hL : L.h ≫ intervalPullbackInputPair f g = (i ▷ (Δ[1] : SSet.{u})) ≫ H.h := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [intervalPullbackInputPair, Category.assoc, lift_fst]
      exact hU.symm
    · simp only [intervalPullbackInputPair, Category.assoc, lift_snd]
      exact hV.symm
  obtain ⟨e, hi, G, hG, hGp⟩ := kanFibration_lift_homotopy_relative
    (intervalPullbackInputPair f g) i a H a₀ L hL
  have he : e ≫ intervalPullbackInputPair f g = lift u v := by
    have h := congrArg (fun r ↦ SSet.ι₁ ≫ r) hGp
    rw [← Category.assoc, G.h₁, H.h₁] at h
    exact h
  refine ⟨e, hi, ?_, ?_, G, hG, hGp⟩
  · have h := congrArg (fun r ↦ r ≫ fst E D) he
    simpa only [intervalPullbackInputPair, Category.assoc, lift_fst] using h
  · have h := congrArg (fun r ↦ r ≫ snd E D) he
    simpa only [intervalPullbackInputPair, Category.assoc, lift_snd] using h

end SerrePositivity.InfinityCategories.F2
