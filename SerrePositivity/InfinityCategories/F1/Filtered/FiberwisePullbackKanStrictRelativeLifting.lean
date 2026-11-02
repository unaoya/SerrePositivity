module

public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.Filtered.FiberwisePullbackKanBoundaryLifting
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.Core.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.IntervalReplacementKan
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.RelativeKanHomotopyStrictification

/-!
概要：任意の有限 Kan 境界を厳密に固定する、実際の引き戻し比較への相対持ち上げ。
方針：任意の境界での円柱付き持ち上げの境界移動を除去する。
規約：境界は元の射に等しく、標的比較は全境界上で定値。
使われ方：一般 coherent filtered 引き戻し比較の弱同値性の境界固定検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：任意の有限 Kan 境界を厳密に固定し、標的では境界固定で元の比較像へ移せる。
方針：円柱付き相対持ち上げと Kan 円柱の境界厳密化。
規約：元の比較射を使用。使われ方：有限境界での比較の相対全射性。 -/
lemma fiberwisePullbackKanComparison_finite_strict_relative_lifting
    {K E D H B : SSet.{u}} [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (A : K.Subcomplex)
    (a : (A : SSet.{u}) ⟶ continuousKanReplacement.obj (fiberwiseIntervalPullback p f g))
    (e : K ⟶ intervalPullback (continuousKanReplacement.map f) (continuousKanReplacement.map g))
    (he : A.ι ≫ e = a ≫ fiberwisePullbackKanComparison p f g) :
    ∃ r : K ⟶ continuousKanReplacement.obj (fiberwiseIntervalPullback p f g),
      A.ι ≫ r = a ∧ ∃ G : SSet.Homotopy e (r ≫ fiberwisePullbackKanComparison p f g),
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h =
          fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ a ≫ fiberwisePullbackKanComparison p f g := by
  obtain ⟨r, L, G, hG⟩ := fiberwisePullbackKanComparison_finite_kan_boundary_lifting p f g A a e he
  exact relativeKanHomotopy_strictification A (fiberwisePullbackKanComparison p f g) a e r he L G hG

end SerrePositivity.InfinityCategories.F2
