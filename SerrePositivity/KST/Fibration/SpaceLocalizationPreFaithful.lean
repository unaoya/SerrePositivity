module
public import SerrePositivity.KST.Fibration.SpaceDiagramPair
public import SerrePositivity.KST.Fibration.UliftLocalizationPreFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-! # 小さい商局所化の前合成は、元の空間値関手 ∞ 圏全体でも充満忠実 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 二つの任意の空間値図式を共通の小さい全充満標的へ入れ、元の全写像空間で反映する。 -/
theorem spaceLocalizationPre_fullyFaithful {X Q : SSet.{u}} [Quasicategory Q]
    (q : X ⟶ Q) (W : Set (X _⦋1⦌)) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre ((SSet.uliftFunctor.{u + 1, u}).map q)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) := by
  intro a b
  obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity).surjective a
  obtain ⟨G, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity).surjective b
  let E := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramTarget (spaceDiagramSum F G)
  let j := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.smallSpaceDiagramInclusion (spaceDiagramSum F G)
  let f := (SSet.uliftFunctor.{u + 1, u}).map (smallSpaceDiagramPairLeft F G)
  let g := (SSet.uliftFunctor.{u + 1, u}).map (smallSpaceDiagramPairRight F G)
  let k := (SSet.uliftFunctor.{u + 1, u}).map q
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful j := smallSpaceDiagramInclusion_isFullyFaithful _
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre k).app ((SSet.uliftFunctor.{u + 1, u}).obj E)) :=
    uliftLocalizationPre_fullyFaithful (E := E) q W hq
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj Q)).map j ≫ (pre k).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) := by
    rw [(pre k).naturality j]
    exact hp.comp (hj.postcompose ((SSet.uliftFunctor.{u + 1, u}).obj X))
  have hc := hh (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap_comp] at hc
  have hs := (hj.postcompose ((SSet.uliftFunctor.{u + 1, u}).obj Q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)
  have ht := hs.cancel_left hc
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap ((pre k).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ j))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ j))) at ht
  have hF : f ≫ j = F := smallSpaceDiagramPairLeft_inclusion F G
  have hG : g ≫ j = G := smallSpaceDiagramPairRight_inclusion F G
  rw [hF, hG] at ht
  exact ht

end SerrePositivity.KST.Fibration
