module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierRightKanUnit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RightKanCriterion
/-!
概要：平坦な Drinfeld 商の dg nerve は、実 Verdier 辺に関する ∞ 圏的局所化。
方針：全標的での実右 Kan 延長・単位可逆性・標準右 Kan 条件を全関手圏の普遍性へ渡す。
規約：任意 quasicategory 標的の全反転関手圏への充満忠実性と本質的全射性。
使われ方：安定 Verdier 商・Verdier 列と平坦分解後の局所化の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
/-- 任意の実分母反転関手は、商上の実関手と全関手圏の一つの実同型を持つ。 -/
lemma dgVerdierInvertingFunctor_extension_iso_exists (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) {Y : SSet.{max u v}} [Quasicategory Y]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) :
    ∃ G : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P ⟶ Y,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P ≫ G) F) := by
  obtain ⟨G, α, hα⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierInvertingFunctor_rightKanExtension_exists A D P hP F hF
  exact ⟨G, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy α
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanUnit_isInvertible A D P hP F hF G α hα)⟩⟩
/-- 商関手の前合成は、任意標的の全反転関手圏へ本質的全射。 -/
lemma dgVerdierLocalizationPrecomposition_isEssentiallySurjective (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (Y : SSet.{max u v}) [Quasicategory Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_invertsVerdierEdges A D P hP) Y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_isEssentiallySurjective_of_extensions
  intro F hF
  exact dgVerdierInvertingFunctor_extension_iso_exists A D P hP F hF
/-- 平坦な Drinfeld 商の dg nerve の射影は、実 Verdier 辺に関する全 ∞ 関手圏の局所化。 -/
lemma dgQuotientNerveProjection_isLocalization (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_invertsVerdierEdges A D P hP, fun Y _ => ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierLocalizationPrecomposition_isFullyFaithful A D P hP Y
  · exact dgVerdierLocalizationPrecomposition_isEssentiallySurjective A D P hP Y
end SerrePositivity.InfinityCategories.Project.DerivedCategories
