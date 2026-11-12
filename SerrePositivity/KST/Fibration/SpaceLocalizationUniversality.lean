module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.SpaceLocalizationUniversality
public import SerrePositivity.KST.Fibration.SpaceLocalizationPreFaithful
public import SerrePositivity.KST.Fibration.SpaceDiagramLocalizationDescent
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge

/-! # 元の小さい商局所化の、宇宙を揃えた空間値関手 ∞ 圏での普遍性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

variable {X Q : SSet.{u}} [Quasicategory Q] (q : X ⟶ Q)
  (W : Set (X _⦋1⦌)) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q W)

/-- 空間値関手 ∞ 圏での元の局所化普遍性。全写像空間の充満忠実性と実因子化から証明する。 -/
theorem spaceLocalizationPrecomposition_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.spaceLocalizationPrecomposition q W hq) := by
  let k := (SSet.uliftFunctor.{u + 1, u}).map q
  let V : Set (((SSet.uliftFunctor.{u + 1, u}).obj X) _⦋1⦌) := ULift.up '' W
  have hi := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj X)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex ((SSet.uliftFunctor.{u + 1, u}).obj X) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity V)
  have hc : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.spaceLocalizationPrecomposition q W hq ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors ((SSet.uliftFunctor.{u + 1, u}).obj X) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity V).ι =
        (pre k).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι k V (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.invertsEdges_ulift q W hq.choose) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
  · apply hi.cancel_right
    exact Eq.mpr (congrArg (fun m => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful m) hc)
      (spaceLocalizationPre_fullyFaithful q W hq)
  · intro v
    obtain ⟨H, hH⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv
      ((SSet.uliftFunctor.{u + 1, u}).obj X) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity).surjective v.val
    have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm v.val) V at hv
    rw [← hH, Equiv.symm_apply_apply] at hv
    let K := spaceDiagramLocalizationDescend q W hq H hv
    have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (k ≫ K) H := spaceDiagramLocalizationDescendIso q W hq H hv
    have he := e ≪≫ eqToIso (congrArg HomotopyCategory.mk hH)
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex K, ⟨hi.preimageVertexIso he⟩⟩

end SerrePositivity.KST.Fibration
