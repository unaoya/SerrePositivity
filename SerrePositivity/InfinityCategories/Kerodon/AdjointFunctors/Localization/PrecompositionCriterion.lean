module
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FunctorExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus
/-!
概要：全前合成の充満忠実性と実延長から局所化を判定する。
方針：反転関手への全包含を消去し、全反転関手圏の同値を得る。
規約：任意の quasicategory 標的。使われ方：平坦分解による局所化の輸送。

対応節は Kerodon 6.3（Tag 01M4）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 全前合成が充満忠実で全反転関手が実延長を持つなら、同じ射は局所化。 -/
lemma isLocalization_of_fullyFaithful_extensions {X Q : SSet.{u}} (q : X ⟶ Q)
    (W : Set (X _⦋1⦌)) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges q W)
    (hf : ∀ (Y : SSet.{u}) [Quasicategory Y], _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre q).app Y))
    (he : ∀ (Y : SSet.{u}) [Quasicategory Y] (F : X ⟶ Y), _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W →
      ∃ G : Q ⟶ Y, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q ≫ G) F)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q W := by
  refine ⟨hq, fun Y _ => ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
  · have hi := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom X).obj Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X Y W)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W).ι at hi
    apply hi.cancel_right
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι]
    exact hf Y
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_isEssentiallySurjective_of_extensions q W hq (he Y)
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
