module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Localization.GroupoidCompletionMaps

/-!
概要：単体集合の元の同型を、両方の実関手を持つ亜群化の同値へ移す。
方針：両合成の厳密な恒等式を亜群化の合成比較で運ぶ。
規約：始域・終域の充填性は不要。使われ方：元の固定端点 span と底変換 fiber の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Localization
open SerrePositivity.KST.LocalizingInvariants

def groupoidCompletionEquivalenceOfIso {X Y : SSet.{u}} (e : X ≅ Y) :
    QCatEquivalence (groupoidCompletion X) (groupoidCompletion Y) where
  hom := groupoidCompletionMapOf e.hom
  inv := groupoidCompletionMapOf e.inv
  homInvIso := groupoidCompletionMapOf_compIso e.hom e.inv ≪≫
    (by rw [e.hom_inv_id]; exact groupoidCompletionMapOf_idIso X)
  invHomIso := groupoidCompletionMapOf_compIso e.inv e.hom ≪≫
    (by rw [e.inv_hom_id]; exact groupoidCompletionMapOf_idIso Y)

end SerrePositivity.InfinityCategories.Derived.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEquivalenceOfIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionEquivalenceOfIso := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEquivalenceOfIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionEquivalenceOfIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEquivalenceOfIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionEquivalenceOfIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEquivalenceOfIso._proof_2
