module
public import SerrePositivity.KST.Fibration.WeakSpanKanValueCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakQuotientMappingComparison

/-! # 元の分数比較の同値性を、同じ商上の coherent な比較へ伝える -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の全固定終点比較が同値なら、同じ全 strict Kan 比較の辺は可逆。 -/
theorem weakSpanKanMappingComparisonEdge_isInvertible_of_fractionComparison
    (hf : ∀ y : B.obj _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionMappingComparison q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (weakSpanKanMappingComparisonEdge h x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramNaturalTransformationEdge_isInvertible
    (F := ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x, trivial⟩)
    (G := ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x, trivial⟩)
    (Functor.whiskerRight (weakSpanKanMappingComparison h x) _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
  intro c
  exact (weakSpanKanMappingComparison_value_equivalence_iff h x c).mpr (hf _)

/-- 同じ全単体上の比較の可逆性は、初頂点局所化の全充満忠実性で底へ降りる。 -/
theorem weakSpanSpaceMappingComparison_isIso_of_fractionComparison
    (hf : ∀ y : B.obj _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionMappingComparison q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y)) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison h x) := by
  have : IsIso (Truncated.HomotopyCategory.homMk
      (weakSpanKanMappingComparisonEdge h x).toTruncated) :=
    weakSpanKanMappingComparisonEdge_isInvertible_of_fractionComparison h x hf
  have hr : IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison_restricted h x) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison_restricted
    infer_instance
  have hm : IsIso
      ((hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)).toFunctor.map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison h x)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison_pre h x).symm ▸ hr
  have hs := (localizationPre_fullyFaithful (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} B.obj)).toHoFullyFaithful
  exact hs.isIso_of_isIso_map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSpaceMappingComparison h x)

/-- 同じ底上の比較の可逆性は、商の全関手 ∞ 圏の充満忠実性で商上へ降りる。 -/
theorem weakQuotientMappingComparison_isIso_of_fractionComparison
    (hf : ∀ y : B.obj _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionMappingComparison q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y)) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison h x) := by
  have := weakSpanSpaceMappingComparison_isIso_of_fractionComparison h x hf
  have hr : IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison_restricted h x) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison_restricted
    infer_instance
  have hm : IsIso
      ((hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map q.hom)).app
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison h x)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison_pre h x).symm ▸ hr
  have hs := spaceLocalizationPre_fullyFaithful q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.quotient
  exact hs.toHoFullyFaithful.isIso_of_isIso_map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison h x)

end SerrePositivity.KST.Fibration
