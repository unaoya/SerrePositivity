module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackKanComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FiberwisePullbackKanStrictRelativeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteRelativeWeakCriterion
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementKan

/-!
概要：一般の filtered な底上の元の三全空間の Kan 引き戻し比較は弱ホモトピー同値。
方針：任意の標準境界に対する厳密な相対持ち上げを path 置換による判定へ渡す。
規約：strict 図式への置換や元の射の fibration 性を仮定しない。
使われ方：一般 coherent filtered 余極限と引き戻しの交換。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：元の全空間 Kan 引き戻し比較は弱ホモトピー同値。
方針：境界固定相対持ち上げから全 path 置換境界を充填する。
規約：元の比較射そのもの。使われ方：native 余極限と引き戻しの比較。 -/
lemma fiberwisePullbackKanComparison_isWeakHomotopyEquivalence {E D H B : SSet.{u}}
    [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B] (p : H ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (f : E ⟶ H) (g : D ⟶ H) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (f ≫ p)] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (g ≫ p)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison p f g) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isWeakHomotopyEquivalence_of_strict_relative_lifting
  intro n a e he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.fiberwisePullbackKanComparison_finite_strict_relative_lifting p f g (boundary n) a e he

/-- 概要：元の Kan 引き戻し比較には実際の単体的ホモトピー逆が存在する。
方針：構成した弱同値と Kan Whitehead 判定。
規約：元の比較の単位上の三座標は保持。使われ方：実際の比較を同値として native 極限へ接続。 -/
lemma fiberwisePullbackKanComparison_isSimplicialHomotopyEquivalence {E D H B : SSet.{u}}
    [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B] (p : H ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (f : E ⟶ H) (g : D ⟶ H) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (f ≫ p)] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (g ≫ p)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackKanComparison p f g) :=
  (fiberwisePullbackKanComparison_isWeakHomotopyEquivalence p f g).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
