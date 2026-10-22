module

public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemLocalColimits
public import SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplittingColimit
public import SerrePositivity.InfinityCategories.F1B.KanLeftStrictExistence

/-!
概要：指定した元の全 Idem 図式が余極限を持てば、元の強い coherent 分裂が存在する。
方針：証明済みの全局所余極限と元の包含の性質を、厳密な左 Kan 延長へ渡す。
規約：構成した分裂は元の全図式を制限で厳密に回収する。
使われ方：HTT 4.4.5.14〜15 の分裂と余極限による冪等完備性の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全 Idem 図式の余極限から、同じ全図式を厳密に回収する強い分裂が存在する。 -/
lemma strongSplitting_exists_of_hasColimit {X : SSet.{u}} [Quasicategory X]
    (d : CoherentIdempotent X) (hd : HasColimit d) : Nonempty (StrongSplitting d) := by
  obtain ⟨F, hF, _hcol⟩ := F1B.exists_kanLeftCanonical_strict_extension_of_local_colimits
    idemInclusion idemInclusion_isFullyFaithful d (idemLocalDiagrams_hasColimit d hd)
  exact ⟨⟨F, hF⟩⟩

/-- 指定した元の全 coherent 冪等図式の強い分裂の存在と、同じ図式の余極限の存在は同値。 -/
lemma nonemptyStrongSplitting_iff_hasColimit {X : SSet.{u}} [Quasicategory X]
    (d : CoherentIdempotent X) : Nonempty (StrongSplitting d) ↔ HasColimit d :=
  ⟨fun ⟨s⟩ ↦ s.hasColimit, strongSplitting_exists_of_hasColimit d⟩

/-- 冪等完備性は、全ての元の coherent 冪等図式の余極限の存在と同値。 -/
lemma isIdempotentComplete_iff_hasColimits (X : SSet.{u}) [Quasicategory X] :
    IsIdempotentComplete X ↔ ∀ d : CoherentIdempotent X, HasColimit d := by
  constructor
  · intro h d
    exact h.hasColimit d
  · intro h d
    exact strongSplitting_exists_of_hasColimit d (h d)

end SerrePositivity.InfinityCategories.F2.Idempotent
