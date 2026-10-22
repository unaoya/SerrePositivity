module
public import SerrePositivity.KST.Fibration.SpaceDiagramPair
public import SerrePositivity.KST.Fibration.UliftLocalizationPreFaithful
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulPostcomposition

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
    (q : X ⟶ Q) (W : Set (X _⦋1⦌)) (hq : IsLocalization q W) :
    IsFullyFaithful ((pre ((SSet.uliftFunctor.{u + 1, u}).map q)).app SpaceInfinity.{u}) := by
  intro a b
  obtain ⟨F, rfl⟩ := (functorVertexEquiv _ SpaceInfinity).surjective a
  obtain ⟨G, rfl⟩ := (functorVertexEquiv _ SpaceInfinity).surjective b
  let E := smallSpaceDiagramTarget (spaceDiagramSum F G)
  let j := smallSpaceDiagramInclusion (spaceDiagramSum F G)
  let f := (SSet.uliftFunctor.{u + 1, u}).map (smallSpaceDiagramPairLeft F G)
  let g := (SSet.uliftFunctor.{u + 1, u}).map (smallSpaceDiagramPairRight F G)
  let k := (SSet.uliftFunctor.{u + 1, u}).map q
  have hj : IsFullyFaithful j := smallSpaceDiagramInclusion_isFullyFaithful _
  have hp : IsFullyFaithful ((pre k).app ((SSet.uliftFunctor.{u + 1, u}).obj E)) :=
    uliftLocalizationPre_fullyFaithful (E := E) q W hq
  have hh : IsFullyFaithful
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj Q)).map j ≫ (pre k).app SpaceInfinity) := by
    rw [(pre k).naturality j]
    exact hp.comp (hj.postcompose ((SSet.uliftFunctor.{u + 1, u}).obj X))
  have hc := hh (functorVertex f) (functorVertex g)
  rw [pinchedHomMap_comp] at hc
  have hs := (hj.postcompose ((SSet.uliftFunctor.{u + 1, u}).obj Q))
    (functorVertex f) (functorVertex g)
  have ht := hs.cancel_left hc
  change IsSimplicialHomotopyEquivalence
    (pinchedHomMap ((pre k).app SpaceInfinity) (functorVertex (f ≫ j))
      (functorVertex (g ≫ j))) at ht
  have hF : f ≫ j = F := smallSpaceDiagramPairLeft_inclusion F G
  have hG : g ≫ j = G := smallSpaceDiagramPairRight_inclusion F G
  rw [hF, hG] at ht
  exact ht

end SerrePositivity.KST.Fibration
