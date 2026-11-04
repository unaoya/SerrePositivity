module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanSpaceMappingComparison
public import SerrePositivity.KST.Fibration.FractionKanQuotientDescent
public import SerrePositivity.KST.Fibration.SpaceLocalizationFactorizationHom

/-! # 元の Verdier 商上の分数図式と coslice 図式を結ぶ、同じ実比較二胞体 -/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
private theorem cancelIsoConjugation {D : Type v} [Category.{w} D]
    {a b c d : D} (e : a ≅ b) (f : c ≅ d) (α : b ⟶ d) :
    e.inv ≫ (e.hom ≫ α ≫ f.inv) ≫ f.hom = α := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の底上の同じ比較を、商からの二つの実制限同型で正規化する。 -/
def weakQuotientMappingComparison_restricted :
    FunctorHom
      ((SSet.uliftFunctor.{u + 1, u}).map q.hom ≫ weakSpanKanQuotientDiagram h x)
      ((SSet.uliftFunctor.{u + 1, u}).map q.hom ≫ fractionKanQuotientDiagram h x) :=
  (weakSpanKanQuotientDiagram_restrictionIso h x).hom ≫ weakSpanSpaceMappingComparison h x ≫
    (fractionKanQuotientDiagram_restrictionIso h x).inv

/-- 同じ比較を、宇宙を揃えた全関手 ∞ 圏の普遍性で元の商上に降下する。 -/
def weakQuotientMappingComparison :
    FunctorHom (weakSpanKanQuotientDiagram h x) (fractionKanQuotientDiagram h x) :=
  spaceLocalizationFactorizationHom q.hom (weakEquivalences i) h.quotient
    (weakQuotientMappingComparison_restricted h x)

/-- 元の商関手で制限すれば、二つの実制限同型を含めた元の比較を厳密に回収する。 -/
theorem weakQuotientMappingComparison_pre :
    (hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map q.hom)).app
      SpaceInfinity)).toFunctor.map (weakQuotientMappingComparison h x) =
        weakQuotientMappingComparison_restricted h x :=
  spaceLocalizationFactorizationHom_map _ _ _ _

/-- 元の実制限同型で正規化すると、底上の元の同じ比較二胞体を厳密に回収する。 -/
theorem weakQuotientMappingComparison_pre_normalized :
    (weakSpanKanQuotientDiagram_restrictionIso h x).inv ≫
      (hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map q.hom)).app
        SpaceInfinity)).toFunctor.map (weakQuotientMappingComparison h x) ≫
          (fractionKanQuotientDiagram_restrictionIso h x).hom =
            weakSpanSpaceMappingComparison h x := by
  have hc := congrArg (fun a : FunctorHom
      ((SSet.uliftFunctor.{u + 1, u}).map q.hom ≫ weakSpanKanQuotientDiagram h x)
      ((SSet.uliftFunctor.{u + 1, u}).map q.hom ≫ fractionKanQuotientDiagram h x) =>
        (weakSpanKanQuotientDiagram_restrictionIso h x).inv ≫ a ≫
          (fractionKanQuotientDiagram_restrictionIso h x).hom)
    (weakQuotientMappingComparison_pre h x)
  exact hc.trans (cancelIsoConjugation (weakSpanKanQuotientDiagram_restrictionIso h x)
    (fractionKanQuotientDiagram_restrictionIso h x) (weakSpanSpaceMappingComparison h x))

/-- 元の商上の比較は、全単体の整合性を保持した実際のホモトピーとして表示できる。 -/
def weakQuotientMappingComparisonHomotopy :
    SSet.Homotopy (weakSpanKanQuotientDiagram h x) (fractionKanQuotientDiagram h x) :=
  functorHomHomotopy (weakQuotientMappingComparison h x)

/-- 選んだ実ホモトピーの類は、商へ降下した同じ比較二胞体と厳密に一致する。 -/
theorem weakQuotientMappingComparisonHomotopy_hom :
    Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (weakQuotientMappingComparisonHomotopy h x)) =
        weakQuotientMappingComparison h x := functorHomHomotopy_hom _

end SerrePositivity.KST.Fibration
