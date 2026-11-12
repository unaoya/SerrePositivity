module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiniteSliceWeakContractibility
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceIdentityTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenALeft

/-! # 有限対充填からの cofinality と弱同値

概要：全時刻整合的な有限対充填を持つ射は、quasicategory 標的に対して left cofinal。
方針：頂点上の slice は終対象付き右ファイブレーションなので、弱可縮な引き戻しを得る。
規約：弱同値は既存の全 Kan 標的の検査の定義を使う。使われ方：実屋根比較の局所化判定。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet

/-- 全時刻整合的な有限対充填は、標的 quasicategory への left cofinality を与える。 -/
lemma HasFiniteHomotopyRelativeFillers.isLeftCofinal {E Q : SSet.{u}} [Quasicategory Q]
    {F : E ⟶ Q} (hF : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.HasFiniteHomotopyRelativeFillers F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_weaklyContractible_slices
  intro q
  exact hF.weaklyContractiblePullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceIdentityCone_isTerminalVertex q)

/-- 有限対充填条件は、全 Kan 標的で検査する元の弱ホモトピー同値性を与える。 -/
lemma HasFiniteHomotopyRelativeFillers.isWeakHomotopyEquivalence
    {E Q : SSet.{u}} [Quasicategory Q] {F : E ⟶ Q}
    (hF : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.HasFiniteHomotopyRelativeFillers F) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence F :=
  hF.isLeftCofinal.isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories
