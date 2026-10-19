module

public import SerrePositivity.InfinityCategories.F1B.KanLeftCanonicalMapping
public import SerrePositivity.InfinityCategories.F1B.KanRightCanonicalMapping
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulFibration

/-!
概要：元の標準 Kan 関手の片側の写像空間の制限は自明 Kan fibration。
方針：証明済みの指定 pinched 比較のホモトピー同値と制限の Kan 性を合わせる。
規約：相手の関手の普遍性は不要、δ は単射とする。
使われ方：Kerodon Corollary 7.3.6.9 の自明 Kan 表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：標準左 Kan 関手から出る制限の指定写像空間作用は自明 Kan。
方針：単射に沿う前合成の inner 性と指定比較のホモトピー同値を使う。
規約：相手 G の普遍性や δ の充満忠実性は不要。
使われ方：左 Kan の写像空間の厳密な可縮性。 -/
lemma kanLeftCanonical_pinchedHomMap_trivialKanFibration {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) [Mono δ] (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, IsColimitCone (leftKanCanonicalCocone δ F c)) (G : C ⟶ D) :
    TrivialKanFibration
      (pinchedHomMap ((pre δ).app D) (functorVertex F) (functorVertex G)) :=
  trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence _
    (kanLeftCanonical_pinchedHomMap_equivalence δ F hF G)

/-- 概要：標準右 Kan 関手へ入る制限の指定写像空間作用は自明 Kan。
方針：制限の Kan 性と右 Kan の指定比較のホモトピー同値を合わせる。
規約：始点 G の普遍性や δ の充満忠実性は不要。
使われ方：右 Kan の写像空間の厳密な可縮性。 -/
lemma kanRightCanonical_pinchedHomMap_trivialKanFibration {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) [Mono δ] (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, IsLimitCone (rightKanCanonicalCone δ F c)) (G : C ⟶ D) :
    TrivialKanFibration
      (pinchedHomMap ((pre δ).app D) (functorVertex G) (functorVertex F)) :=
  trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence _
    (kanRightCanonical_pinchedHomMap_equivalence δ F hF G)

end SerrePositivity.InfinityCategories.F1B
