module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.FilteredDiagonalCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationCofinalPullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalWeakEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakFunctoriality

/-!
概要：有限形状では、fiber ごとの関手から全関手空間への射は right cofinal。
方針：定値図式関手の cofinality を内部 Hom の left fibration に沿って引き戻す。
規約：底は一般の filtered ∞ 圏。
使われ方：底を固定した path 模型から全空間の path 模型への比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：有限形状の底を定値に固定する射は right cofinal。
方針：有限形状への対角の cofinality と left fibration に沿う底変換を使う。
規約：元の関手空間への第一射影。使われ方：fiber ごとの path の全空間比較。 -/
lemma fiberwiseFunctorToFunctor_isRightCofinal {E B : SSet.{u}}
    [Quasicategory B] [IsFilteredInfinity B] (p : E ⟶ B) [LeftFibration p]
    (K : SSet.{u}) [K.Finite] :
    IsRightCofinal (pullback.fst ((ihom K).map p) (constantDiagram K B)) :=
  leftFibration_pullback_isRightCofinal _ _ (isRightCofinal_constantDiagram_of_filtered K B)

/-- 概要：有限形状の定値底の制限は全関手空間への弱同値。
方針：元の比較射の cofinality を弱同値へ移す。
規約：全関手空間を Kan と仮定しない。使われ方：path 模型の比較。 -/
lemma fiberwiseFunctorToFunctor_isWeakHomotopyEquivalence {E B : SSet.{u}}
    [Quasicategory B] [IsFilteredInfinity B] (p : E ⟶ B) [LeftFibration p]
    (K : SSet.{u}) [K.Finite] :
    IsWeakHomotopyEquivalence (pullback.fst ((ihom K).map p) (constantDiagram K B)) :=
  (fiberwiseFunctorToFunctor_isRightCofinal p K).isWeakHomotopyEquivalence

/-- 概要：定値底の有限関手空間比較の Kan 置換は実際のホモトピー同値。
方針：元の弱同値を連続 Kan 置換で保存し、Kan 対象間の Whitehead を使う。
規約：置換した比較射は元の第一射影の像。使われ方：有限 path 比較の一因子。 -/
lemma fiberwiseFunctorToFunctorKan_homotopyEquivalence {E B : SSet.{u}}
    [Quasicategory B] [IsFilteredInfinity B] (p : E ⟶ B) [LeftFibration p]
    (K : SSet.{u}) [K.Finite] :
    IsSimplicialHomotopyEquivalence (continuousKanReplacement.map
      (pullback.fst ((ihom K).map p) (constantDiagram K B))) :=
  (continuousKanReplacement_map_isWeakHomotopyEquivalence _
    (fiberwiseFunctorToFunctor_isWeakHomotopyEquivalence p K)).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
