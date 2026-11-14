module

public import SerrePositivity.KST.NonConnective.DGKappaSuspension
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectModulesInfinity

/-!
概要：小さい dg cone 内の perfect 安定閉包と、β5 の元の Perf の比較を明示入力にする。
方針：全写像空間の同値と D(D) への包含の全関手比較を要求する。
規約：通常の導来圏での perfect 比較だけで、この ∞ 比較を完成扱いしない。
使われ方：構成した同じ平坦商を D(D)^κ／Perf(D) として利用するための意味の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ full dg cone の、β5 の実半自由模型への比較。 -/
def dgKappaConeDerivedComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D I) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (ModuleCategory R D) I.objects) ≫
    dgConeModuleDerived R D

/-- この全関手比較の充満忠実性は、未供給の模型の明示入力に保持した条件。 -/
lemma dgKappaConeDerivedComparison_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgKappaConeDerivedComparison R D I) := I.derivedFullyFaithful

/-- β5 の実 Perf と、商で零化する同じ小さい安定閉包との、未供給の比較入力。 -/
structure DGKappaPerfectInput where
  /-- 元の実 Perf から、同じ dg cone 内の perfect 安定閉包への実関手。 -/
  comparison : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R D ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)
  /-- 通常の Hom ではなく、全写像空間での実 ∞ 圏同値。 -/
  isEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence comparison
  /-- 同じ実半自由模型への包含は、元の β5 の Perf 包含と全関手で一致する。 -/
  inclusion : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((comparison ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I)
      (dgKappaConePerfectObjects R D I)) ≫ dgKappaConeDerivedComparison R D I)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R D)

/-- 元の Perf を、入力した同じ全関手比較を通して dg cone に含める実関手。 -/
def dgKappaPerfectInclusion (P : DGKappaPerfectInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D I) :=
  P.comparison ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I)
    (dgKappaConePerfectObjects R D I)

/-- 同じ懸垂の商射影は、元の Perf の全頂点を実際に零化する。 -/
lemma dgKappaSuspension_kills_perfect (P : DGKappaPerfectInput R D I)
    (z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R D) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((dgKappaPerfectInclusion R D I P ≫ dgKappaSuspensionProjection R D I).app
      (Opposite.op ⦋0⦌) z) := by
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R (DGKappaCone R D I)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureNerve_isStable R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)
  let := dgKappaSuspensionInfinity_isStable R D I
  exact (dgKappaSuspension_isStableVerdierSequence R D I).kills
    (P.comparison.app (Opposite.op ⦋0⦌) z)

end SerrePositivity.KST.NonConnective
