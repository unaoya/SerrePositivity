module
public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UliftPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.UniverseFullyFaithful

/-! # 小さい局所化標的への前合成の全写像空間の充満忠実性の宇宙移送 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の局所化の全関手圏の前合成は、持ち上げた同じ小さい標的でも充満忠実。 -/
theorem uliftLocalizationPre_fullyFaithful {X Q E : SSet.{u}}
    [Quasicategory Q] [Quasicategory E] (q : X ⟶ Q) (W : Set (X _⦋1⦌))
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre ((SSet.uliftFunctor.{v, u}).map q)).app
      ((SSet.uliftFunctor.{v, u}).obj E)) := by
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso.{u, v} Q E
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso.{u, v} X E
  have hc : a.inv ≫ (SSet.uliftFunctor.{v, u}).map ((pre q).app E) ≫ b.hom =
      (pre ((SSet.uliftFunctor.{v, u}).map q)).app ((SSet.uliftFunctor.{v, u}).obj E) := by
    exact (congrArg (fun m => a.inv ≫ m)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.uliftFunctorSpaceIso_pre.{u, v} (Z := E) q).symm).trans
        (Iso.inv_hom_id_assoc a _)
  rw [← hc]
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso a.symm).isQCatEquivalence.isFullyFaithful).comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsFullyFaithful.ulift (localizationPre_fullyFaithful q W hq)).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso b).isQCatEquivalence.isFullyFaithful)

end SerrePositivity.KST.Fibration
