module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeRightFunctorTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeTerminalMapping

/-!
概要：元の相対右 Kan 関手へ入る相対制限の指定右 pinched 比較の同値。
方針：反転による相対終対象性と、終対象へ入る右模型の自然な比較を合わせる。
規約：始点の関手には Kan 条件を要求しない。
使われ方：Kerodon Proposition 7.3.6.7（Tag 030F） の右側の isofibration 上の片側比較。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：標準相対右 Kan 関手へ任意の関手から入る相対写像空間の制限はホモトピー同値。
方針：元の相対制限に関する相対終対象性を右 pinched 作用の同値へ渡す。
規約：G の局所普遍性だけを使い、相手 H の普遍性は仮定しない。
使われ方：右 Kan の片側の相対普遍性。 -/
lemma kanRelativeRightFunctor_relative_pinchedHomMap_equivalence {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (s : internalHom.PullbackObjObj δ U) (H G : C ⟶ D)
    (hlim : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeRightKanExtendedFrom U δ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap s.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) := by
  have : InnerFibration U := hU.innerFibration
  have : Quasicategory s.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory U δ s
  have : Quasicategory ((internalHom.obj (Opposite.op C)).obj D) :=
    inferInstanceAs (Quasicategory ((ihom C).obj D))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeTerminalVertex_pinchedHomMap_equivalence s.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightFunctor_relative_terminal δ hδ U hU s G hlim) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
