module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.Cofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenA
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenANecessary
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.DiagonalCommaWeakContractibility
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredWeakContractibility
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.KappaFilteredCoslices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplicialShapes
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：filtered ∞ 圏の有限形状への対角関手と、κ 版の対角関手は right cofinal。
方針：標準 comma と元の coslice の弱可縮性の比較に Quillen A を適用する。
規約：一般の coherent な図式を試験し、通常の圏の nerve に限定しない。
使われ方：filtered 余極限と有限極限の交換の添字の比較。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：対角関手の right cofinality は全ての形状 K の coslice の弱可縮性と同値。
方針：標準 comma の比較と Quillen A を双方向に使う。
規約：K の有限性はこの判定自体には不要。使われ方：filtered 性の対角判定。 -/
@[kerodon 02P4]
lemma isRightCofinal_constantDiagram_iff (K C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K C) ↔
      ∀ p : K ⟶ C, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) := by
  constructor
  · intro h p
    exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weaklyContractible_diagonalStandardComma_iff p).1
      (h.coslice_isWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))
  · intro h
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_weaklyContractible_coslices
    intro v
    obtain ⟨p, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K C).surjective v
    exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weaklyContractible_diagonalStandardComma_iff p).2 (h p)

/-- 概要：filtered ∞ 圏の有限形状への対角関手は right cofinal。
方針：有限図式の coslice の弱可縮性を対角関手の判定に渡す。
規約：有限形状は一般の有限単体集合。使われ方：Kerodon 9.1.1.18（Tag 02PJ） の十分性。 -/
lemma isRightCofinal_constantDiagram_of_filtered (K C : SSet.{u}) [K.Finite]
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity C] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K C) :=
  (isRightCofinal_constantDiagram_iff K C).2 _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_sliceUnder_of_filtered

/-- 概要：正則 κ と κ-small な形状に対して κ-filtered ∞ 圏の対角関手は right cofinal。
方針：κ-small な図式の coslice の弱可縮性を同じ判定に使う。
規約：κ の正則性と形状の小ささを明示。使われ方：Indκ の filtered 添字。 -/
lemma isRightCofinal_constantDiagram_of_kappaFiltered {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (K C : SSet.{u}) (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K C) :=
  (isRightCofinal_constantDiagram_iff K C).2
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_sliceUnder_of_kappaFiltered hκ hK)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
