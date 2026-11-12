module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ConeRestrictionCocartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CocartesianTerminalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorConeTerminalBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：通常の点ごとの極限性から関手 ∞ 圏の極限性を得る。
方針：錐の制限の cocartesian 性で極限錐を相対境界充填へ移し、評価ごとの相対充填を関手圏へ移送する。
規約：点ごとの仮定は通常の IsLimitCone。
使われ方：HTT Proposition 5.1.2.2、Kerodon Corollary 7.1.8.15（Tag 02XP） の双対。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：極限錐は錐の制限射の上で終点境界を充填する。
方針：slice と錐の fiber の同値で終対象へ移し、cocartesian な輸送による相対充填を使う。
規約：X は quasicategory、添字 K は任意。
使われ方：Kerodon Proposition 7.1.6.13（Tag 02XB） の絶対極限の場合。 -/
lemma terminalBoundaryLifting_coneRestriction_of_isLimitCone {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_of_isTerminalVertex_fiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv p c) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_isTerminalVertex_coneFamily c).1 hc)

/-- 概要：極限錐であることは錐の制限の相対終点境界充填と同値。
方針：極限性からの輸送による方向と fiber への制限による方向を合わせる。
規約：X は quasicategory、添字 K は任意。
使われ方：Kerodon Proposition 7.1.6.13（Tag 02XB） の相対終対象による極限判定。 -/
@[kerodon 02XD]
lemma isLimitCone_iff_terminalBoundaryLifting_coneRestriction {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val) :=
  ⟨terminalBoundaryLifting_coneRestriction_of_isLimitCone c,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_terminalBoundaryLifting_coneRestriction c⟩

/-- 概要：すべての頂点で極限錐となる関手圏の錐は極限錐。
方針：評価した通常の極限錐を相対境界充填へ移し、関手圏への相対充填の移送を適用する。
規約：X は quasicategory、J と K は任意、追加の相対充填の仮定は不要。
使われ方：HTT Proposition 5.1.2.2、Kerodon Corollary 7.1.8.15（Tag 02XP） の双対。 -/
@[kerodon 02XP]
lemma isLimitCone_of_pointwise {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseLimitCone c) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_pointwise_terminalBoundaryLifting c
  intro k
  exact terminalBoundaryLifting_coneRestriction_of_isLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone c k) (hc k)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
