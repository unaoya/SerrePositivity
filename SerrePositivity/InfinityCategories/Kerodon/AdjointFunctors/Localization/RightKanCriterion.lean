module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightPrecompositionFaithful
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FunctorExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightExistence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
/-!
概要：右 Kan の局所極限と実単位成分から、全関手 ∞ 圏での局所化普遍性を導く。
方針：既存の全関手への右 Kan 組み立てを使い、全標的の充満忠実性と反転関手への本質的全射性を証明する。
規約：局所極限・標準右 Kan 条件・単位の可逆性は実証すべき仮定。
使われ方：実 Verdier 分母の cofinal 計算を IsLocalization 本体へ渡す入口。

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
/-- 反転関手の局所右 Kan 極限と実単位成分の可逆性から、実延長と全関手同型を構成する。 -/
lemma invertingFunctor_extension_of_rightKan_local_limits {X Q Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] [Quasicategory Y]
    (q : X ⟶ Q) (F : X ⟶ Y)
    (hlim : ∀ z : Q _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram q F z))
    (hunit : ∀ (G : Q ⟶ Y) (α : SSet.Homotopy (q ≫ G) F),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension q F G α → ∀ x : X _⦋0⦌,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α x).toTruncated) :
    ∃ G : Q ⟶ Y, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q ≫ G) F) := by
  obtain ⟨G, α, hα⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRightExtension_of_local_limits q F hlim
  exact ⟨G, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy α (hunit G α hα)⟩⟩
/-- 全標的での実右 Kan 計算は、前合成の全関手 ∞ 圏での局所化普遍性を与える。 -/
lemma isLocalization_of_rightKan_local_limits {X Q : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] (q : X ⟶ Q) (W : Set (X _⦋1⦌))
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges q W)
    (hcanonical : ∀ (Y : SSet.{u}) [Quasicategory Y], ∀ G : Q ⟶ Y,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension q (q ≫ G) G (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (q ≫ G)))
    (hlim : ∀ (Y : SSet.{u}) [Quasicategory Y], ∀ F : X ⟶ Y, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W →
      ∀ z : Q _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram q F z))
    (hunit : ∀ (Y : SSet.{u}) [Quasicategory Y], ∀ (F : X ⟶ Y), _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W →
      ∀ (G : Q ⟶ Y) (α : SSet.Homotopy (q ≫ G) F), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension q F G α →
        ∀ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge α x).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q W := by
  refine ⟨hq, fun Y _ => ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.localizationPrecomposition_isFullyFaithful_of_rightKan q W hq hcanonical Y
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_isEssentiallySurjective_of_extensions
    intro F hF
    exact invertingFunctor_extension_of_rightKan_local_limits q F (hlim Y F hF) (hunit Y F hF)
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
