module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramStandardCoconeColimit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowDiagramFiltered

/-!
概要：指定した全図式を頂点とする単一 κ-filtered Yoneda 表示を記述する。
方針：小さい実 comma の filtered 性と各頂点評価の共終性を同じ標準余錐へ適用する。
規約：一般形状では二条件を明示し、射形状では証明済みの結論を渡す。
使われ方：有限半順序図式の表示から有限余極限の構成への公開界面。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)

/-- 概要：元の全図式そのものの、小さい単一 filtered 表示。
方針：全図式 Yoneda を使用。規約：頂点は厳密に指定。使われ方：有限存在の構成。 -/
def HasSingleFilteredDiagramPresentation : Prop :=
  ∃ (I : SSet.{u}) (hI : Quasicategory I),
    letI := hI
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I ∧
    ∃ a : I ⟶ (ihom K).obj C, ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone
      ((SSet.uliftFunctor.{u + 1, u}).map a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda κ K C),
      c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c

/-- 概要：同じ実添字の二条件から、元の全図式の単一表示を得る。
方針：標準余錐を使用。規約：追加の形状仮定を隠さない。使われ方：形状帰納の帰結。 -/
lemma hasSingleFilteredDiagramPresentation_of_evaluation_cofinal
    (hκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramComma κ D))
    (h : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaEvaluation κ D k)) :
    HasSingleFilteredDiagramPresentation κ D :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramComma κ D, inferInstance, hκ, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaProjection κ D,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaCocone κ D, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaCocone_vertex κ D,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaCocone_isColimit_of_evaluation_cofinal κ D h⟩

/-- 概要：任意の元の射図式は単一 κ-filtered Yoneda 表示を持つ。
方針：両端評価の共終性を適用。規約：元の頂点を保持。使われ方：有限形状の出発点。 -/
lemma indArrow_has_singleFilteredDiagramPresentation [Fact κ.IsRegular]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) :
    HasSingleFilteredDiagramPresentation κ D :=
  hasSingleFilteredDiagramPresentation_of_evaluation_cofinal κ D
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallArrowDiagramComma_isKappaFiltered κ D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaEvaluation_interval_isRightCofinal κ D)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
