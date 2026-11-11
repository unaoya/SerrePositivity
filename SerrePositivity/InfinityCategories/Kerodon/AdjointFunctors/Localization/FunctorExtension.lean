module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
/-!
概要：任意の反転関手の実延長と関手同型から、全反転関手 ∞ 圏への前合成の本質的全射性を得る。
方針：反転頂点を元の実関手で表し、全包含の充満忠実性で指定同型を部分圏へ持ち上げる。
規約：延長は任意の quasicategory 標的。使われ方：局所化普遍性の本質的全射性。

対応節は Kerodon 6.3（Tag 01M4）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 任意反転関手の関手同型付き実延長は、全反転関手 ∞ 圏への本質的全射性を与える。 -/
lemma localizationPrecomposition_isEssentiallySurjective_of_extensions {X Q Y : SSet.{u}}
    [Quasicategory Y] (q : X ⟶ Q) (W : Set (X _⦋1⦌)) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges q W)
    (h : ∀ (F : X ⟶ Y), _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W →
      ∃ G : Q ⟶ Y, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q ≫ G) F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition q W hq Y) := by
  intro b
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X Y).symm b.val
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = b.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X Y).apply_symm_apply b.val
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex b
  obtain ⟨G, ⟨I⟩⟩ := h F hb
  let a := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition q W hq Y).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)
  have ha : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W).ι.app (Opposite.op ⦋0⦌) a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (q ≫ G) :=
    congrArg (fun f => f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι q W hq Y)
  let J : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W).ι.app (Opposite.op ⦋0⦌) a)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W).ι.app (Opposite.op ⦋0⦌) b) :=
    eqToIso (congrArg HomotopyCategory.mk ha) ≪≫ I ≪≫
      eqToIso (congrArg HomotopyCategory.mk hv)
  let ff := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι ((ihom X).obj Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X Y W)).toHoFullyFaithful
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G, ⟨ff.preimageIso J⟩⟩
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
