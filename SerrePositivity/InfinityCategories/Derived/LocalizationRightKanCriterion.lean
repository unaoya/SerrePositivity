module
public import SerrePositivity.InfinityCategories.Derived.RightKanPrecompositionFaithful
public import SerrePositivity.InfinityCategories.Derived.LocalizationFunctorExtension
public import SerrePositivity.InfinityCategories.F1B.KanRightExistence
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
/-!
概要：右 Kan の局所極限と実単位成分から、全関手 ∞ 圏での局所化普遍性を導く。
方針：既存の全関手への右 Kan 組み立てを使い、全標的の充満忠実性と反転関手への本質的全射性を証明する。
規約：局所極限・標準右 Kan 条件・単位の可逆性は実証すべき仮定。
使われ方：実 Verdier 分母の cofinal 計算を IsLocalization 本体へ渡す入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
/-- 反転関手の局所右 Kan 極限と実単位成分の可逆性から、実延長と全関手同型を構成する。 -/
lemma invertingFunctor_extension_of_rightKan_local_limits {X Q Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] [Quasicategory Y]
    (q : X ⟶ Q) (F : X ⟶ Y)
    (hlim : ∀ z : Q _⦋0⦌, HasLimit (rightKanDiagram q F z))
    (hunit : ∀ (G : Q ⟶ Y) (α : SSet.Homotopy (q ≫ G) F),
      IsRightKanExtension q F G α → ∀ x : X _⦋0⦌,
        IsInvertibleEdge (simplicialHomotopyVertexEdge α x).toTruncated) :
    ∃ G : Q ⟶ Y, Nonempty (FunctorIso (q ≫ G) F) := by
  obtain ⟨G, α, hα⟩ := F1B.exists_kanRightExtension_of_local_limits q F hlim
  exact ⟨G, ⟨functorIsoOfPointwiseInvertibleHomotopy α (hunit G α hα)⟩⟩
/-- 全標的での実右 Kan 計算は、前合成の全関手 ∞ 圏での局所化普遍性を与える。 -/
lemma isLocalization_of_rightKan_local_limits {X Q : SSet.{u}}
    [Quasicategory X] [Quasicategory Q] (q : X ⟶ Q) (W : Set (X _⦋1⦌))
    (hq : InvertsEdges q W)
    (hcanonical : ∀ (Y : SSet.{u}) [Quasicategory Y], ∀ G : Q ⟶ Y,
      IsRightKanExtension q (q ≫ G) G (functorHomotopyRefl (q ≫ G)))
    (hlim : ∀ (Y : SSet.{u}) [Quasicategory Y], ∀ F : X ⟶ Y, InvertsEdges F W →
      ∀ z : Q _⦋0⦌, HasLimit (rightKanDiagram q F z))
    (hunit : ∀ (Y : SSet.{u}) [Quasicategory Y], ∀ (F : X ⟶ Y), InvertsEdges F W →
      ∀ (G : Q ⟶ Y) (α : SSet.Homotopy (q ≫ G) F), IsRightKanExtension q F G α →
        ∀ x : X _⦋0⦌, IsInvertibleEdge (simplicialHomotopyVertexEdge α x).toTruncated) :
    IsLocalization q W := by
  refine ⟨hq, fun Y _ => ?_⟩
  apply isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
  · exact localizationPrecomposition_isFullyFaithful_of_rightKan q W hq hcanonical Y
  · apply localizationPrecomposition_isEssentiallySurjective_of_extensions
    intro F hF
    exact invertingFunctor_extension_of_rightKan_local_limits q F (hlim Y F hF) (hunit Y F hF)
end SerrePositivity.InfinityCategories
