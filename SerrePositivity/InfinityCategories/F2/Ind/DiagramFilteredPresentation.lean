module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramStandardCoconeColimit
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowDiagramFiltered

/-!
概要：指定した全図式を頂点とする単一 κ-filtered Yoneda 表示を記述する。
方針：小さい実 comma の filtered 性と各頂点評価の共終性を同じ標準余錐へ適用する。
規約：一般形状では二条件を明示し、射形状では証明済みの結論を渡す。
使われ方：有限半順序図式の表示から有限余極限の構成への公開界面。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)

/-- 概要：元の全図式そのものの、小さい単一 filtered 表示。
方針：全図式 Yoneda を使用。規約：頂点は厳密に指定。使われ方：有限存在の構成。 -/
def HasSingleFilteredDiagramPresentation : Prop :=
  ∃ (I : SSet.{u}) (hI : Quasicategory I),
    letI := hI
    IsKappaFiltered κ I ∧
    ∃ a : I ⟶ (ihom K).obj C, ∃ c : JoinCocone
      ((SSet.uliftFunctor.{u + 1, u}).map a ≫ diagramYoneda κ K C),
      c.vertex = functorVertex D ∧ IsColimitCone c

/-- 概要：同じ実添字の二条件から、元の全図式の単一表示を得る。
方針：標準余錐を使用。規約：追加の形状仮定を隠さない。使われ方：形状帰納の帰結。 -/
lemma hasSingleFilteredDiagramPresentation_of_evaluation_cofinal
    (hκ : IsKappaFiltered κ (smallDiagramComma κ D))
    (h : ∀ k : K _⦋0⦌, IsRightCofinal (smallDiagramCommaEvaluation κ D k)) :
    HasSingleFilteredDiagramPresentation κ D :=
  ⟨smallDiagramComma κ D, inferInstance, hκ, smallDiagramCommaProjection κ D,
    smallDiagramCommaCocone κ D, smallDiagramCommaCocone_vertex κ D,
    smallDiagramCommaCocone_isColimit_of_evaluation_cofinal κ D h⟩

/-- 概要：任意の元の射図式は単一 κ-filtered Yoneda 表示を持つ。
方針：両端評価の共終性を適用。規約：元の頂点を保持。使われ方：有限形状の出発点。 -/
lemma indArrow_has_singleFilteredDiagramPresentation [Fact κ.IsRegular]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C) :
    HasSingleFilteredDiagramPresentation κ D :=
  hasSingleFilteredDiagramPresentation_of_evaluation_cofinal κ D
    (smallArrowDiagramComma_isKappaFiltered κ D)
    (smallDiagramCommaEvaluation_interval_isRightCofinal κ D)

end SerrePositivity.InfinityCategories.F2.Ind
