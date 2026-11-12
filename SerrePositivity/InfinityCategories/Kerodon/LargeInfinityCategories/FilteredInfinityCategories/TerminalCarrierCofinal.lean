module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalCarrierCosliceFiltered
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenA

/-!
概要：全鎖の実現空間の元の値写像は right cofinal。
方針：同じ値写像の全 coslice 引き戻しの弱可縮性を既存の Quillen A に適用する。
規約：ラベルの非空性は正則濃度の下界から証明し、追加仮定にしない。
使われ方：同じ包含順の nerve からの写像との比較による cofinal 添字の構成。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 正則濃度以上のラベル集合は非空。 -/
lemma nonempty_labels_of_regular_bound {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {T : Type u} (hT : κ ≤ Cardinal.mk T) : Nonempty T :=
  Cardinal.mk_ne_zero_iff.mp (ne_of_gt
    (lt_of_lt_of_le (lt_of_lt_of_le Cardinal.aleph0_pos hκ.aleph0_le) hT))

/-- 元のラベル付き積への同じ値写像は right cofinal。 -/
lemma terminalSubcomplexCarrierValue_isRightCofinal {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C]
    {T : Type u} (hT : κ ≤ Cardinal.mk T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexCarrierValue κ (C ⊗ nerve (Codiscrete T))) := by
  have := nonempty_labels_of_regular_bound hκ hT
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_weaklyContractible_coslices
  intro x
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCoslice_isWeaklyContractible hκ hT (SSet.yonedaEquiv.symm x)

/-- 元の底への同じ値写像とラベル射影の合成も right cofinal。 -/
lemma terminalSubcomplexCarrierBase_isRightCofinal {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ C]
    {T : Type u} (hT : κ ≤ Cardinal.mk T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalSubcomplexCarrierValue κ (C ⊗ nerve (Codiscrete T)) ≫
      fst C (nerve (Codiscrete T))) := by
  have := nonempty_labels_of_regular_bound hκ hT
  exact (terminalSubcomplexCarrierValue_isRightCofinal hκ hT).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.codiscreteProductProjection_isRightCofinal C T)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
