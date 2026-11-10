module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InverseAttachmentLifting
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：辺反転の実貼合せは、指定辺集合に対する全関手 ∞ 圏の局所化普遍性を持つ。
方針：元の制限の全単射相対充填を trivial Kan fibration の判定に渡す。
規約：貼合せの quasicategory 性は主張しない。使われ方：inner anodyne 置換後の一般商。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
variable (X : SSet.{u}) (W : Set (X _⦋1⦌))

instance inverseAttachmentRestriction_trivialKanFibration (Y : SSet.{u}) [Quasicategory Y] :
    TrivialKanFibration (inverseAttachmentRestriction X W Y) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  exact inverseAttachmentRestriction_lifting W (boundary n).ι

@[kerodon 01N0]
lemma inverseAttachment_isLocalization : IsLocalization (inverseAttachmentInclusion X W) W := by
  refine ⟨inverseAttachment_inverts X W, fun Y _ => ?_⟩
  change IsQCatEquivalence (inverseAttachmentRestriction X W Y)
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
