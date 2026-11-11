module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CellDGResolutionVerdierEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientExactFunctorEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PrecompositionCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SourceEquivalencePrecomposition
/-!
概要：平坦分解後の dg 商は、元の dg nerve の Verdier 辺に関する実局所化。
方針：cell 増大の同値で全前合成と全反転関手の実延長を輸送する。
規約：元の Hom の平坦性を要求しない。使われ方：一般の安定 Verdier 商。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalClosed SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 平坦分解後の商による全前合成は、任意標的に対して充満忠実。 -/
lemma resolvedDGQuotientPrecomposition_isFullyFaithful (P : Set D)
    (Y : SSet.{max u v}) [Quasicategory Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor A D P)).app Y) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated A D
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.precomposition_isFullyFaithful_of_sourceEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection A D P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientPrecomposition_isFullyFaithful A _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat A D P) Y)
/-- 元の全実 Verdier 辺を反転する任意関手は、平坦分解後の商上の実延長同型を持つ。 -/
lemma resolvedDGVerdierFunctor_extension_exists (P : Set D) {Y : SSet.{max u v}}
    [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) :
    ∃ G : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve A D P ⟶ Y,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor A D P ≫ G) F) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated A D
  obtain ⟨G, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierInvertingFunctor_extension_iso_exists A
    (DGCategoryCellResolution.Source A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects A D P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat A D P) _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellAugmentation_precomp_inverts A D P F hF)
  exact ⟨G, ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.extensionIsoOfSourceEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence A D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection A D P) F G e⟩⟩
/-- 元の Hom の平坦性を仮定せず、平坦分解後の実商は全 ∞ 関手圏の局所化。 -/
theorem resolvedDGQuotientFunctor_isLocalization (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor A D P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_of_fullyFaithful_extensions _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_invertsVerdierEdges A D P)
    (resolvedDGQuotientPrecomposition_isFullyFaithful A D P)
    (fun _ _ => resolvedDGVerdierFunctor_extension_exists A D P)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
