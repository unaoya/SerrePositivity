module

public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.F2.Filtered.FiberwisePullbackKanRelativeDetection
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackValueKanComparison
public import SerrePositivity.InfinityCategories.F2.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram

/-!
概要：任意の有限標的射を、元の境界の全円柱とともに実際の全空間 Kan 比較へ持ち上げる。
方針：元の一値での相対検出を、元の包含と単位へ合成する。
規約：持ち上げの比較円柱の制限は元の境界円柱の像に厳密に一致。
使われ方：一般 coherent filtered 引き戻し比較の弱同値性の相対検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の境界を持つ任意の有限標的射に、境界円柱を保持する相対 Kan 持ち上げがある。
方針：元の値の相対検出を全空間に含める。
規約：元の比較射を使用。使われ方：境界を同時に制御する弱同値性の検査。 -/
lemma fiberwisePullbackKanComparison_finite_relative_lifting
    {K E D H B : SSet.{u}} [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (A : K.Subcomplex)
    (a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g)
    (e : K ⟶ intervalPullback (continuousKanReplacement.map f) (continuousKanReplacement.map g))
    (he : A.ι ≫ e = a ≫ continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
      fiberwisePullbackKanComparison p f g) :
    ∃ r : K ⟶ continuousKanReplacement.obj (fiberwiseIntervalPullback p f g),
      ∃ L : SSet.Homotopy
        (a ≫ continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g)) (A.ι ≫ r),
      ∃ G : SSet.Homotopy e (r ≫ fiberwisePullbackKanComparison p f g),
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫ fiberwisePullbackKanComparison p f g := by
  obtain ⟨b, t, w, hw, L, G, hG⟩ :=
    fiberwisePullbackKanComparison_finite_relative_value_detection p f g A a e he
  let r := w ≫ fiberwisePullbackValueToTotal p f g b ≫
    continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g)
  have hr : A.ι ≫ r = t ≫ fiberwisePullbackValueToTotal p f g b ≫
      continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) := by
    dsimp only [r]
    rw [← Category.assoc A.ι w, hw]
  let L' : SSet.Homotopy
      (a ≫ continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g)) (A.ι ≫ r) :=
    { h := L.h ≫ continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g)
      h₀ := by
        change SSet.ι₀ ≫ L.h ≫ continuousKanReplacementUnit.app
          (fiberwiseIntervalPullback p f g) = a ≫
            continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g)
        rw [← Category.assoc, L.h₀]
      h₁ := by
        change SSet.ι₁ ≫ L.h ≫ continuousKanReplacementUnit.app
          (fiberwiseIntervalPullback p f g) = A.ι ≫ r
        rw [← Category.assoc, L.h₁, hr, Category.assoc]
      rel := (functorHomotopyPostcomp L (continuousKanReplacementUnit.app _)).rel }
  refine ⟨r, L', G, ?_⟩
  exact hG.trans (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.F2
