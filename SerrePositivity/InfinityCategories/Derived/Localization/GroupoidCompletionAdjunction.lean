module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Localization.GroupoidCompletionMaps
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.F1B.Adjunction.Adjunction

/-!
概要：実随伴の両関手は、亜群化後に互いに逆の同値を与える。
方針：Kan 値の自然変換を可逆にし、局所化の普遍性で単位・余単位の同型を降ろす。
規約：元の両関手の亜群化を保持。使われ方：分母上の両側輸送の亜群化の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.F1B
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Localization
open SerrePositivity.KST.LocalizingInvariants

def groupoidCompletionMapOf_functorHomIso {X Y : SSet.{u}} {f g : X ⟶ Y}
    (α : FunctorHom f g) : FunctorIso (groupoidCompletionMapOf f) (groupoidCompletionMapOf g) := by
  apply localizationFactorizationIso _ _ (groupoidCompletion_isLocalization X)
  have : IsGroupoid (hoFunctor.obj ((ihom X).obj (groupoidCompletion Y))) :=
    kanComplex_ho_isGroupoid _
  have : IsIso (homPost (groupoidCompletionMap Y) α) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj ((ihom X).obj (groupoidCompletion Y))) _
  exact groupoidCompletionMapOfIso f ≪≫ asIso (homPost (groupoidCompletionMap Y) α) ≪≫
    (groupoidCompletionMapOfIso g).symm

def groupoidCompletionEquivalenceOfAdjunction {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) : QCatEquivalence (groupoidCompletion X) (groupoidCompletion Y) where
  hom := groupoidCompletionMapOf F
  inv := groupoidCompletionMapOf G
  homInvIso := groupoidCompletionMapOf_compIso F G ≪≫
    (groupoidCompletionMapOf_functorHomIso a.unitHom).symm ≪≫ groupoidCompletionMapOf_idIso X
  invHomIso := groupoidCompletionMapOf_compIso G F ≪≫
    groupoidCompletionMapOf_functorHomIso a.counitHom ≪≫ groupoidCompletionMapOf_idIso Y

lemma groupoidCompletionMapOf_adjunction_isEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) : IsSimplicialHomotopyEquivalence (groupoidCompletionMapOf F) :=
  (groupoidCompletionEquivalenceOfAdjunction a).isQCatEquivalence
    |>.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Derived.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEquivalenceOfAdjunction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionEquivalenceOfAdjunction := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEquivalenceOfAdjunction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionMapOf_adjunction_isEquivalence := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf_adjunction_isEquivalence

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf_functorHomIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionMapOf_functorHomIso := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf_functorHomIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionMapOf_functorHomIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf_functorHomIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionMapOf_functorHomIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf_functorHomIso._proof_2
