module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCanonicalMapping
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightCanonicalMapping
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulFibration
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の標準 Kan 関手の片側の写像空間の制限は自明 Kan fibration。
方針：証明済みの指定 pinched 比較のホモトピー同値と制限の Kan 性を合わせる。
規約：相手の関手の普遍性は不要、δ は単射とする。
使われ方：Kerodon Corollary 7.3.6.9（Tag 030M） の自明 Kan 表示。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：標準左 Kan 関手から出る制限の指定写像空間作用は自明 Kan。
方針：単射に沿う前合成の inner 性と指定比較のホモトピー同値を使う。
規約：相手 G の普遍性や δ の充満忠実性は不要。
使われ方：左 Kan の写像空間の厳密な可縮性。 -/
@[kerodon 030M]
lemma kanLeftCanonical_pinchedHomMap_trivialKanFibration {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) [Mono δ] (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c)) (G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap ((pre δ).app D) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCanonical_pinchedHomMap_equivalence δ F hF G)

/-- 概要：標準右 Kan 関手へ入る制限の指定写像空間作用は自明 Kan。
方針：制限の Kan 性と右 Kan の指定比較のホモトピー同値を合わせる。
規約：始点 G の普遍性や δ の充満忠実性は不要。
使われ方：右 Kan の写像空間の厳密な可縮性。 -/
@[kerodon 030M]
lemma kanRightCanonical_pinchedHomMap_trivialKanFibration {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) [Mono δ] (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c)) (G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap ((pre δ).app D) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightCanonical_pinchedHomMap_equivalence δ F hF G)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
