module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackKanUnit
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackPathPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanCospanPoint

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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：実際の Kan 比較との可換式は指定 path の全境界式を与える。
方針：path 射影と curry の単射性。規約：有限性不要。使われ方：元の境界付き比較の入力。 -/
lemma kanCospanPoint_relative_boundary_path {K A E D H B : SSet.{u}}
    (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (i : A ⟶ K)
    (u : K ⟶ E) (v : K ⟶ D) (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g)
    (P : SSet.Homotopy (u ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H)
      (v ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H))
    (ha : i ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint f g u v P = a ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison p f g) :
    ((Δ[1] : SSet.{u}) ◁ i) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ P.h =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H := by
  have hp := congrArg (fun r ↦ r ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g)) ha
  have hup : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison p f g ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map g) =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackPath p f g ≫
        pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram Δ[1] B) ≫
          (ihom (Δ[1] : SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath, Category.assoc] using
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison_unit_path p f g
  simp only [Category.assoc] at hp
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanCospanPoint_path, hup] at hp
  apply curry_injective
  rw [curry_natural_left, curry_natural_right (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app H), _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism, curry_uncurry]
  simpa only [Category.assoc] using hp

end SerrePositivity.InfinityCategories.Project.FilteredExchange
