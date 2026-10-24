module
public import SerrePositivity.InfinityCategories.Derived.CellDGResolutionVerdierEdges
public import SerrePositivity.InfinityCategories.Derived.DGQuotientExactFunctorEquivalence
public import SerrePositivity.InfinityCategories.F1B.Localization.PrecompositionCriterion
public import SerrePositivity.InfinityCategories.Derived.SourceEquivalencePrecomposition
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve MonoidalClosed SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
/-- 平坦分解後の商による全前合成は、任意標的に対して充満忠実。 -/
lemma resolvedDGQuotientPrecomposition_isFullyFaithful (P : Set D)
    (Y : SSet.{max u v}) [Quasicategory Y] :
    IsFullyFaithful ((pre (resolvedDGQuotientFunctor A D P)).app Y) := by
  let := dgCellResolutionSource_isDGPretriangulated A D
  exact precomposition_isFullyFaithful_of_sourceEquivalence
    (dgCellResolutionNerveEquivalence A D) (resolvedDGQuotientProjection A D P)
    (dgQuotientPrecomposition_isFullyFaithful A _ _ (resolvedDGQuotient_localKFlat A D P) Y)
/-- 元の全実 Verdier 辺を反転する任意関手は、平坦分解後の商上の実延長同型を持つ。 -/
lemma resolvedDGVerdierFunctor_extension_exists (P : Set D) {Y : SSet.{max u v}}
    [Quasicategory Y] (F : dgNerve A D ⟶ Y) (hF : InvertsEdges F (dgVerdierEdges A D P)) :
    ∃ G : resolvedDGQuotientNerve A D P ⟶ Y,
      Nonempty (FunctorIso (resolvedDGQuotientFunctor A D P ≫ G) F) := by
  let := dgCellResolutionSource_isDGPretriangulated A D
  obtain ⟨G, ⟨e⟩⟩ := dgVerdierInvertingFunctor_extension_iso_exists A
    (DGCategoryCellResolution.Source A D) (resolvedDGNullObjects A D P)
    (resolvedDGQuotient_localKFlat A D P) _ (dgCellAugmentation_precomp_inverts A D P F hF)
  exact ⟨G, ⟨extensionIsoOfSourceEquivalence (dgCellResolutionNerveEquivalence A D)
    (resolvedDGQuotientProjection A D P) F G e⟩⟩
/-- 元の Hom の平坦性を仮定せず、平坦分解後の実商は全 ∞ 関手圏の局所化。 -/
theorem resolvedDGQuotientFunctor_isLocalization (P : Set D) :
    IsLocalization (resolvedDGQuotientFunctor A D P) (dgVerdierEdges A D P) :=
  isLocalization_of_fullyFaithful_extensions _ _
    (resolvedDGQuotientFunctor_invertsVerdierEdges A D P)
    (resolvedDGQuotientPrecomposition_isFullyFaithful A D P)
    (fun _ _ => resolvedDGVerdierFunctor_extension_exists A D P)
end SerrePositivity.InfinityCategories
