module

public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness
public import SerrePositivity.KST.LocalizingInvariants.NerveFullyFaithfulReflection

/-!
概要：全関手 ∞ 圏の局所化は、h 圏から任意通常圏への前合成を充満忠実にする。
方針：nerve を標的とする普遍性を指数比較の自然性で共役し、通常の充満忠実性へ戻す。
規約：自然変換全体を扱う。本質像の反転関手との一致は後続。
使われ方：商の h 圏の通常局所化普遍性と実辺の分数表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma localizationHoPre_nerve_fullyFaithful {X Q : SSet.{u}} [Quasicategory Q]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W)
    (A : Type u) [Category.{u} A] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (nerveMap ((Functor.whiskeringLeft
      (hoFunctor.obj X) (hoFunctor.obj Q) A).obj (hoFunctor.map F).toFunctor)) := by
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (homotopyNerveExponentialIso X A).hom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (homotopyNerveExponentialIso X A)).isFullyFaithful
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (homotopyNerveExponentialIso Q A).hom :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (homotopyNerveExponentialIso Q A)).isFullyFaithful
  apply hx.cancel_right
  rw [homotopyNerveExponentialIso_precomp]
  exact hq.comp (localizationPre_fullyFaithful F W hF)

def localizationHoPre_fullyFaithful {X Q : SSet.{u}} [Quasicategory Q]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W)
    (A : Type u) [Category.{u} A] :
    ((Functor.whiskeringLeft (hoFunctor.obj X) (hoFunctor.obj Q) A).obj
      (hoFunctor.map F).toFunctor).FullyFaithful :=
  fullyFaithful_of_nerveMap _ (localizationHoPre_nerve_fullyFaithful F W hF A)

end SerrePositivity.KST.LocalizingInvariants
