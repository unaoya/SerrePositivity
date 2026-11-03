module

public import SerrePositivity.InfinityCategories.F2.Idempotent.OppositeIdempotent
public import SerrePositivity.InfinityCategories.F1B.Idempotent.StrongSplittingExistence
public import SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplittingLimit

/-!
概要：指定した元の全 Idem 図式の極限から、同じ図式の厳密な強い分裂が存在する。
方針：元の反転図式の余極限に証明済みの存在定理を適用し、元の包含の正方形で戻す。
規約：元の全図式の制限を厳密に回収する。
使われ方：HTT 4.4.5.14〜15 の分裂・余極限・極限による判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全 Idem 図式の極限から、同じ全図式を厳密に回収する強い分裂が存在する。 -/
lemma strongSplitting_exists_of_hasLimit {X : SSet.{u}} [Quasicategory X]
    (d : CoherentIdempotent X) (hd : HasLimit d) : Nonempty (StrongSplitting d) := by
  obtain ⟨s⟩ := strongSplitting_exists_of_hasColimit (oppositeIdempotent d)
    (oppositeIdempotent_hasColimit_of_hasLimit d hd)
  exact ⟨oppositeIdempotentSplittingToOriginal s⟩

/-- 指定した元の全 coherent 冪等図式の強い分裂の存在と、同じ図式の極限の存在は同値。 -/
lemma nonemptyStrongSplitting_iff_hasLimit {X : SSet.{u}} [Quasicategory X]
    (d : CoherentIdempotent X) : Nonempty (StrongSplitting d) ↔ HasLimit d :=
  ⟨fun ⟨s⟩ ↦ s.hasLimit, strongSplitting_exists_of_hasLimit d⟩

/-- 冪等完備性は、全ての元の coherent 冪等図式の極限の存在と同値。 -/
lemma isIdempotentComplete_iff_hasLimits (X : SSet.{u}) [Quasicategory X] :
    IsIdempotentComplete X ↔ ∀ d : CoherentIdempotent X, HasLimit d := by
  constructor
  · intro h d
    exact h.hasLimit d
  · intro h d
    exact strongSplitting_exists_of_hasLimit d (h d)

end SerrePositivity.InfinityCategories.F2.Idempotent
