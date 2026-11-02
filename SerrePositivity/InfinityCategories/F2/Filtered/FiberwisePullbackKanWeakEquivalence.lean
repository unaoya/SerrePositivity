module

public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopy
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakWhitehead
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.F2.Filtered.FiberwisePullbackKanStrictRelativeLifting
public import SerrePositivity.InfinityCategories.F2.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.FiniteRelativeWeakCriterion
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.IntervalReplacementKan

/-!
概要：一般の filtered な底上の元の三全空間の Kan 引き戻し比較は弱ホモトピー同値。
方針：任意の標準境界に対する厳密な相対持ち上げを path 置換による判定へ渡す。
規約：strict 図式への置換や元の射の fibration 性を仮定しない。
使われ方：一般 coherent filtered 余極限と引き戻しの交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の全空間 Kan 引き戻し比較は弱ホモトピー同値。
方針：境界固定相対持ち上げから全 path 置換境界を充填する。
規約：元の比較射そのもの。使われ方：native 余極限と引き戻しの比較。 -/
lemma fiberwisePullbackKanComparison_isWeakHomotopyEquivalence {E D H B : SSet.{u}}
    [Quasicategory B] [IsFilteredInfinity B] (p : H ⟶ B) [LeftFibration p]
    (f : E ⟶ H) (g : D ⟶ H) [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] :
    IsWeakHomotopyEquivalence (fiberwisePullbackKanComparison p f g) := by
  apply isWeakHomotopyEquivalence_of_strict_relative_lifting
  intro n a e he
  exact fiberwisePullbackKanComparison_finite_strict_relative_lifting p f g (boundary n) a e he

/-- 概要：元の Kan 引き戻し比較には実際の単体的ホモトピー逆が存在する。
方針：構成した弱同値と Kan Whitehead 判定。
規約：元の比較の単位上の三座標は保持。使われ方：実際の比較を同値として native 極限へ接続。 -/
lemma fiberwisePullbackKanComparison_isSimplicialHomotopyEquivalence {E D H B : SSet.{u}}
    [Quasicategory B] [IsFilteredInfinity B] (p : H ⟶ B) [LeftFibration p]
    (f : E ⟶ H) (g : D ⟶ H) [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] :
    IsSimplicialHomotopyEquivalence (fiberwisePullbackKanComparison p f g) :=
  (fiberwisePullbackKanComparison_isWeakHomotopyEquivalence p f g).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
