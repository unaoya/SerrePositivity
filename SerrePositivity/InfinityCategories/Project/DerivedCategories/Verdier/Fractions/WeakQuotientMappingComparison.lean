module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakSpanSpaceMappingComparison
public import SerrePositivity.KST.Fibration.FractionKanQuotientDescent
public import SerrePositivity.KST.Fibration.SpaceLocalizationFactorizationHom

/-! # 元の Verdier 商上の分数図式と coslice 図式を結ぶ、同じ実比較二胞体 -/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
private theorem cancelIsoConjugation {D : Type v} [Category.{w} D]
    {a b c d : D} (e : a ≅ b) (f : c ≅ d) (α : b ⟶ d) :
    e.inv ≫ (e.hom ≫ α ≫ f.inv) ≫ f.hom = α := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の底上の同じ比較を、商からの二つの実制限同型で正規化する。 -/
def weakQuotientMappingComparison_restricted :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
      ((SSet.uliftFunctor.{u + 1, u}).map q.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x)
      ((SSet.uliftFunctor.{u + 1, u}).map q.hom ≫ fractionKanQuotientDiagram h x) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram_restrictionIso h x).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison h x ≫
    (fractionKanQuotientDiagram_restrictionIso h x).inv

/-- 同じ比較を、宇宙を揃えた全関手 ∞ 圏の普遍性で元の商上に降下する。 -/
def weakQuotientMappingComparison :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x) (fractionKanQuotientDiagram h x) :=
  spaceLocalizationFactorizationHom q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.quotient
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison_restricted h x)

/-- 元の商関手で制限すれば、二つの実制限同型を含めた元の比較を厳密に回収する。 -/
theorem weakQuotientMappingComparison_pre :
    (hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map q.hom)).app
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison h x) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison_restricted h x :=
  spaceLocalizationFactorizationHom_map _ _ _ _

/-- 元の実制限同型で正規化すると、底上の元の同じ比較二胞体を厳密に回収する。 -/
theorem weakQuotientMappingComparison_pre_normalized :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram_restrictionIso h x).inv ≫
      (hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map q.hom)).app
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison h x) ≫
          (fractionKanQuotientDiagram_restrictionIso h x).hom =
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison h x := by
  have hc := congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
      ((SSet.uliftFunctor.{u + 1, u}).map q.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x)
      ((SSet.uliftFunctor.{u + 1, u}).map q.hom ≫ fractionKanQuotientDiagram h x) =>
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram_restrictionIso h x).inv ≫ a ≫
          (fractionKanQuotientDiagram_restrictionIso h x).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison_pre h x)
  exact hc.trans (cancelIsoConjugation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram_restrictionIso h x)
    (fractionKanQuotientDiagram_restrictionIso h x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison h x))

/-- 元の商上の比較は、全単体の整合性を保持した実際のホモトピーとして表示できる。 -/
def weakQuotientMappingComparisonHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x) (fractionKanQuotientDiagram h x) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison h x)

/-- 選んだ実ホモトピーの類は、商へ降下した同じ比較二胞体と厳密に一致する。 -/
theorem weakQuotientMappingComparisonHomotopy_hom :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparisonHomotopy h x)) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison h x := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
