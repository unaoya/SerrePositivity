module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafRepresentableEdgeDetection

/-!
概要：表現可能前層からの元の写像空間の後合成が、前層の辺の可逆性を検出する。
方針：元の Yoneda 評価の全族自然性で各点の Kan 射に移し、点ごとの可逆性を適用する。
規約：自然性や検出性を入力に加えない。
使われ方：G14 の反映した表現可能生成族による検出。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding


/-- 全表現可能前層からの元の後合成の同値性は、前層のホモトピー圏の射の可逆性を検出。 -/
lemma presheafHom_isIso_of_representable_post {C : SSet.{u}} [Quasicategory C]
    {x z : (PresheafInfinity C) _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj (PresheafInfinity C)) ⟶ HomotopyCategory.mk z)
    (h : ∀ y : C _⦋0⦌, IsQCatEquivalence
      (postcompose (functorVertex (representablePresheafInfinity y)) f)) : IsIso f := by
  obtain ⟨F, hx⟩ := (presheafInfinityObjectEquiv C).surjective x
  obtain ⟨G, hz⟩ := (presheafInfinityObjectEquiv C).surjective z
  change functorVertex F = x at hx
  change functorVertex G = z at hz
  subst x
  subst z
  obtain ⟨e, he⟩ := homotopyCategory_homMk_surjective (functorVertex F) (functorVertex G) f
  have hi := presheafEdge_isInvertible_of_representable_post F G (SSet.Edge.ofTruncated e)
    (by intro y; simpa only [SSet.Edge.ofTruncated, SSet.Edge.toTruncated, he] using h y)
  change IsIso (SSet.Truncated.HomotopyCategory.homMk e) at hi
  rwa [he] at hi

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
