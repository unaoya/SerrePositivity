module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Core.CatInfinity.ConstantDiagram
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackKanUnit
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.KanCospanPoint

/-!
概要：元の比較射による境界可換式から全 path の厳密な境界式を回収する。
方針：単位上の全 path の式と curry の単射性を使う。
規約：元の境界射を保持。使われ方：座標の追加仮定を要しない相対有限比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：実際の Kan 比較との可換式は指定 path の全境界式を与える。
方針：path 射影と curry の単射性。規約：有限性不要。使われ方：元の境界付き比較の入力。 -/
lemma kanCospanPoint_relative_boundary_path {K A E D H B : SSet.{u}}
    (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (i : A ⟶ K)
    (u : K ⟶ E) (v : K ⟶ D) (a : A ⟶ fiberwiseIntervalPullback p f g)
    (P : SSet.Homotopy (u ≫ f ≫ continuousKanReplacementUnit.app H)
      (v ≫ g ≫ continuousKanReplacementUnit.app H))
    (ha : i ≫ kanCospanPoint f g u v P = a ≫
      continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
        fiberwisePullbackKanComparison p f g) :
    ((Δ[1] : SSet.{u}) ◁ i) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ P.h =
      fiberwisePullbackPathPrism p f g a ≫ continuousKanReplacementUnit.app H := by
  have hp := congrArg (fun r ↦ r ≫ intervalPullbackPath
    (continuousKanReplacement.map f) (continuousKanReplacement.map g)) ha
  have hup : continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
      fiberwisePullbackKanComparison p f g ≫ intervalPullbackPath
        (continuousKanReplacement.map f) (continuousKanReplacement.map g) =
      fiberwiseIntervalPullbackPath p f g ≫
        pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) ≫
          (ihom (Δ[1] : SSet.{u})).map (continuousKanReplacementUnit.app H) := by
    simpa only [intervalPullbackPath, Category.assoc] using
      fiberwisePullbackKanComparison_unit_path p f g
  simp only [Category.assoc] at hp
  rw [kanCospanPoint_path, hup] at hp
  apply curry_injective
  rw [curry_natural_left, curry_natural_right (fiberwisePullbackPathPrism p f g a)
    (continuousKanReplacementUnit.app H), fiberwisePullbackPathPrism, curry_uncurry]
  simpa only [Category.assoc] using hp

end SerrePositivity.InfinityCategories.F2
