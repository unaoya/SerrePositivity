module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteGeneratorPresentation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplicialShapes
public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.Comma.CardinalArrow
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
概要：κ-small な単体集合は、通常の単体集合の圏で正則 κ に対して κ-presentable。
方針：κ 個未満の有限生成部分複体の余極限表示と、有限表示性の濃度に関する単調性を使う。
規約：κ-small 性は F2N-1 の非退化単体による定義をそのまま使う。
使われ方：κ-small な形状から κ-filtered 余極限への相対因子分解。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 任意の無限濃度 κ 未満の型の有限部分集合全体も、同じ κ 未満。 -/
lemma cardinal_finset_lt {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {A : Type u} (hA : Cardinal.mk A < κ) : Cardinal.mk (Finset A) < κ := by
  classical
  rcases finite_or_infinite A with h | h
  · have := h
    let := Fintype.ofFinite A
    exact lt_of_lt_of_le (Cardinal.mk_lt_aleph0_iff.mpr inferInstance) hκ
  · have := h
    rwa [Cardinal.mk_finset_of_infinite]

/-- 元の κ-small な単体集合の有限生成部分複体を添字付ける型は κ 未満。 -/
lemma finiteGeneratorIndex_cardinal_lt {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) : Cardinal.mk (Finset K.N) < κ :=
  cardinal_finset_lt hκ hK

/-- 同じ有限生成部分複体の添字圏の全ての射も κ 個未満。 -/
lemma finiteGeneratorIndex_arrow_small {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) : HasCardinalLT (Arrow (Finset K.N)) κ :=
  (hasCardinalLT_arrow_iff_of_isThin _ κ hκ).mpr
    ((hasCardinalLT_iff_cardinal_mk_lt _ _).mpr (finiteGeneratorIndex_cardinal_lt hκ hK))

/-- 正則 κ に対して、元の κ-small な単体集合からの Hom は通常の κ-filtered 余極限を保つ。 -/
lemma isCardinalPresentable_of_isKappaSmall {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) : IsCardinalPresentable K κ := by
  have hκ : κ.IsRegular := Fact.out
  have := Cardinal.fact_isRegular_aleph0.{u}
  have (s : Finset K.N) : IsCardinalPresentable ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.finiteGeneratorDiagram K).obj s) κ := by
    change IsCardinalPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.finiteGeneratorSubcomplex K s).toSSet κ
    exact isCardinalPresentable_of_le (κ := Cardinal.aleph0) _ hκ.aleph0_le
  exact isCardinalPresentable_of_isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.finiteGeneratorCocone K)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.finiteGeneratorCocone_isColimit K) κ (finiteGeneratorIndex_arrow_small hκ.aleph0_le hK)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
