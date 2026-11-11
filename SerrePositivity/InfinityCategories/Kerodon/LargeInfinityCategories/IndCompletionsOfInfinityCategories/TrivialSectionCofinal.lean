module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.SectionCosliceTrivial
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenA

/-!
概要：trivial Kan 射影の任意の厳密な切断は right cofinal。
方針：同じ切断の各 coslice を、底の弱可縮な coslice と trivial Kan 射影で比較する。
規約：切断を別の逆射へ取り替えず、同値性を追加仮定にしない。
使われ方：保存済みの包含順の nerve からの写像自体の cofinal 性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 同じ trivial Kan 射影の同じ厳密な切断に Quillen A を適用する。 -/
lemma isRightCofinal_section_of_trivialKanFibration {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal s := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_weaklyContractible_coslices
  intro e
  let a := SSet.yonedaEquiv.symm e
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionCosliceMap_trivialKanFibration a p s hs
  have hw :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionCosliceMap a p s)).isWeakHomotopyEquivalence
  apply hw.weaklyContractible_iff.mpr
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnder_isWeaklyContractible (SSet.yonedaEquiv (a ≫ p))
  simpa only [SSet.yonedaEquiv.symm_apply_apply] using hb

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
