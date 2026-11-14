module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.OppositeIdempotent
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingExistence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingLimit
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：指定した元の全 Idem 図式の極限から、同じ図式の厳密な強い分裂が存在する。
方針：元の反転図式の余極限に証明済みの存在定理を適用し、元の包含の正方形で戻す。
規約：元の全図式の制限を厳密に回収する。
使われ方：HTT 4.4.5.14〜15 の分裂・余極限・極限による判定。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の全 Idem 図式の極限から、同じ全図式を厳密に回収する強い分裂が存在する。 -/
lemma strongSplitting_exists_of_hasLimit {X : SSet.{u}} [Quasicategory X]
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit d) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) := by
  obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplitting_exists_of_hasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oppositeIdempotent d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oppositeIdempotent_hasColimit_of_hasLimit d hd)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.oppositeIdempotentSplittingToOriginal s⟩

/-- 指定した元の全 coherent 冪等図式の強い分裂の存在と、同じ図式の極限の存在は同値。 -/
@[kerodon 0403]
lemma nonemptyStrongSplitting_iff_hasLimit {X : SSet.{u}} [Quasicategory X]
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit d :=
  ⟨fun ⟨s⟩ ↦ s.hasLimit, strongSplitting_exists_of_hasLimit d⟩

/-- 冪等完備性は、全ての元の coherent 冪等図式の極限の存在と同値。 -/
@[kerodon 040C]
lemma isIdempotentComplete_iff_hasLimits (X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X ↔ ∀ d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit d := by
  constructor
  · intro h d
    exact h.hasLimit d
  · intro h d
    exact strongSplitting_exists_of_hasLimit d (h d)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.4.5.14"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.nonemptyStrongSplitting_iff_hasLimit
attribute [cite HTT "4.4.5.15"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isIdempotentComplete_iff_hasLimits
