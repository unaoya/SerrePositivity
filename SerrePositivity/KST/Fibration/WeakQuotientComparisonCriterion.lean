module
public import SerrePositivity.KST.Fibration.WeakSpanKanValueCriterion
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakQuotientMappingComparison

/-! # 元の分数比較の同値性を、同じ商上の coherent な比較へ伝える -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の全固定終点比較が同値なら、同じ全 strict Kan 比較の辺は可逆。 -/
theorem weakSpanKanMappingComparisonEdge_isInvertible_of_fractionComparison
    (hf : ∀ y : B.obj _⦋0⦌,
      IsQCatEquivalence (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y)) :
    IsInvertibleEdge (weakSpanKanMappingComparisonEdge h x) := by
  apply kanDiagramNaturalTransformationEdge_isInvertible
    (F := ⟨weakSpanKanDiagram i x, trivial⟩)
    (G := ⟨fractionSimplexKanMappingDiagram q.hom x, trivial⟩)
    (Functor.whiskerRight (weakSpanKanMappingComparison h x) kanObjectForget)
  intro c
  exact (weakSpanKanMappingComparison_value_equivalence_iff h x c).mpr (hf _)

/-- 同じ全単体上の比較の可逆性は、初頂点局所化の全充満忠実性で底へ降りる。 -/
theorem weakSpanSpaceMappingComparison_isIso_of_fractionComparison
    (hf : ∀ y : B.obj _⦋0⦌,
      IsQCatEquivalence (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y)) :
    IsIso (weakSpanSpaceMappingComparison h x) := by
  have : IsIso (Truncated.HomotopyCategory.homMk
      (weakSpanKanMappingComparisonEdge h x).toTruncated) :=
    weakSpanKanMappingComparisonEdge_isInvertible_of_fractionComparison h x hf
  have hr : IsIso (weakSpanSpaceMappingComparison_restricted h x) := by
    unfold _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison_restricted
    infer_instance
  have hm : IsIso
      ((hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map
        (transportSimplexFirstVertexMap B.obj))).app SpaceInfinity)).toFunctor.map
          (weakSpanSpaceMappingComparison h x)) :=
    (weakSpanSpaceMappingComparison_pre h x).symm ▸ hr
  have hs := (localizationPre_fullyFaithful (Y := SpaceInfinity.{u}) _ _
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} B.obj)).toHoFullyFaithful
  exact hs.isIso_of_isIso_map (weakSpanSpaceMappingComparison h x)

/-- 同じ底上の比較の可逆性は、商の全関手 ∞ 圏の充満忠実性で商上へ降りる。 -/
theorem weakQuotientMappingComparison_isIso_of_fractionComparison
    (hf : ∀ y : B.obj _⦋0⦌,
      IsQCatEquivalence (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y)) :
    IsIso (weakQuotientMappingComparison h x) := by
  have := weakSpanSpaceMappingComparison_isIso_of_fractionComparison h x hf
  have hr : IsIso (weakQuotientMappingComparison_restricted h x) := by
    unfold _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakQuotientMappingComparison_restricted
    infer_instance
  have hm : IsIso
      ((hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map q.hom)).app
        SpaceInfinity)).toFunctor.map (weakQuotientMappingComparison h x)) :=
    (weakQuotientMappingComparison_pre h x).symm ▸ hr
  have hs := spaceLocalizationPre_fullyFaithful q.hom (weakEquivalences i) h.quotient
  exact hs.toHoFullyFaithful.isIso_of_isIso_map (weakQuotientMappingComparison h x)

end SerrePositivity.KST.Fibration
