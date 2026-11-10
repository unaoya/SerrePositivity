module

public import SerrePositivity.InfinityCategories.Core.ConeRestrictionCocartesianFibration
public import SerrePositivity.InfinityCategories.Core.CocartesianTerminalBoundary
public import SerrePositivity.InfinityCategories.Core.FunctorConeTerminalBoundary
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：通常の点ごとの極限性から関手 ∞ 圏の極限性を得る。
方針：錐の制限の cocartesian 性で極限錐を相対境界充填へ移し、評価ごとの相対充填を関手圏へ移送する。
規約：点ごとの仮定は通常の IsLimitCone。
使われ方：HTT Proposition 5.1.2.2、Kerodon Proposition 7.1.8.5 の極限側。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：極限錐は錐の制限射の上で終点境界を充填する。
方針：slice と錐の fiber の同値で終対象へ移し、cocartesian な輸送による相対充填を使う。
規約：X は quasicategory、添字 K は任意。
使われ方：Kerodon Proposition 7.1.6.13 の絶対極限の場合。 -/
lemma terminalBoundaryLifting_coneRestriction_of_isLimitCone {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) (hc : IsLimitCone c) :
    TerminalBoundaryLifting (coneRestriction K X) (functorVertex c.val) := by
  exact terminalBoundaryLifting_of_isTerminalVertex_fiber (coneRestriction K X) (functorVertex p)
    (coneFamilyVertexEquiv p c) ((isLimitCone_iff_isTerminalVertex_coneFamily c).1 hc)

/-- 概要：極限錐であることは錐の制限の相対終点境界充填と同値。
方針：極限性からの輸送による方向と fiber への制限による方向を合わせる。
規約：X は quasicategory、添字 K は任意。
使われ方：Kerodon Proposition 7.1.6.13 の相対終対象による極限判定。 -/
@[kerodon 02XD]
lemma isLimitCone_iff_terminalBoundaryLifting_coneRestriction {K X : SSet.{u}}
    [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ TerminalBoundaryLifting (coneRestriction K X) (functorVertex c.val) :=
  ⟨terminalBoundaryLifting_coneRestriction_of_isLimitCone c,
    isLimitCone_of_terminalBoundaryLifting_coneRestriction c⟩

/-- 概要：すべての頂点で極限錐となる関手圏の錐は極限錐。
方針：評価した通常の極限錐を相対境界充填へ移し、関手圏への相対充填の移送を適用する。
規約：X は quasicategory、J と K は任意、追加の相対充填の仮定は不要。
使われ方：HTT Proposition 5.1.2.2、Kerodon Proposition 7.1.8.5 の極限側。 -/
@[kerodon 02XP]
lemma isLimitCone_of_pointwise {J K X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (c : JoinCone p) (hc : IsPointwiseLimitCone c) : IsLimitCone c := by
  apply isLimitCone_of_pointwise_terminalBoundaryLifting c
  intro k
  exact terminalBoundaryLifting_coneRestriction_of_isLimitCone (evaluateFunctorCone c k) (hc k)

end SerrePositivity.InfinityCategories
