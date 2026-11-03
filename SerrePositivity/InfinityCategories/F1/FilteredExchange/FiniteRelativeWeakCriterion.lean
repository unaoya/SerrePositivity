module

public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopy
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.IntervalReplacementKan
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.IntervalReplacementRelativeLifting
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.IntervalReplacementSection

/-!
概要：全標準境界での境界固定相対持ち上げから弱ホモトピー同値性を証明する。
方針：区間 path 置換の終点射の全境界充填性を示し、定値切断の弱同値性と合成する。
規約：有限写像空間の π₀ の全単射だけからは結論しない。
使われ方：一般 coherent filtered 引き戻しの実際の Kan 比較の検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：全標準境界で相対的に持ち上がれば、path 置換の終点射は自明 Kan fibration。
方針：元の全境界 path を保持する厳密持ち上げを全境界テストへ渡す。
規約：零次元も含む。使われ方：実際の比較の弱同値性の証明。 -/
lemma intervalReplacementEndpoint_trivialKanFibration_of_strict_relative_lifting
    {X Y : SSet.{u}} [KanComplex Y] (f : X ⟶ Y)
    (h : ∀ (n : ℕ) (a : (boundary n : SSet.{u}) ⟶ X) (b : (Δ[n] : SSet.{u}) ⟶ Y),
      (boundary n).ι ≫ b = a ≫ f → ∃ r : (Δ[n] : SSet.{u}) ⟶ X,
        (boundary n).ι ≫ r = a ∧ ∃ G : SSet.Homotopy b (r ≫ f),
          ((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫ G.h =
            fst (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ a ≫ f) :
    TrivialKanFibration (intervalReplacementEndpoint f) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  obtain ⟨v, hv, hvp⟩ := intervalReplacementEndpoint_relative_lift (boundary n) f a b sq.w (h n)
  exact CommSq.HasLift.mk' ⟨v, hv, hvp⟩

/-- 概要：Kan 対象間の境界固定相対持ち上げは、全 Kan 標的による弱同値性を導く。
方針：path 置換の終点射と定値切断の弱同値性を合成する。
規約：全境界の円柱条件を使用。使われ方：元の引き戻し比較への有限相対検査の適用。 -/
lemma isWeakHomotopyEquivalence_of_strict_relative_lifting
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    (h : ∀ (n : ℕ) (a : (boundary n : SSet.{u}) ⟶ X) (b : (Δ[n] : SSet.{u}) ⟶ Y),
      (boundary n).ι ≫ b = a ≫ f → ∃ r : (Δ[n] : SSet.{u}) ⟶ X,
        (boundary n).ι ≫ r = a ∧ ∃ G : SSet.Homotopy b (r ≫ f),
          ((boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫ G.h =
            fst (boundary n : SSet.{u}) (Δ[1] : SSet.{u}) ≫ a ≫ f) :
    IsWeakHomotopyEquivalence f := by
  have := intervalReplacementEndpoint_trivialKanFibration_of_strict_relative_lifting f h
  have hp := (isQCatEquivalence_of_trivialKanFibration
    (intervalReplacementEndpoint f)).isWeakHomotopyEquivalence
  have hf := (intervalReplacementSection_isWeakHomotopyEquivalence f).comp hp
  rwa [intervalReplacementSection_endpoint] at hf

end SerrePositivity.InfinityCategories.F2
