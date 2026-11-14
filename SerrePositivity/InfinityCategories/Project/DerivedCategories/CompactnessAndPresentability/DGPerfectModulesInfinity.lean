module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.DGSemifreeProjectiveEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGClosedModuleFunctorExact
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
/-!
概要：任意の小さい dg 圏の Perf の実安定 ∞ 圏と、D(D) への実完全充満忠実関手。
方針：既存の射影的 perfect dg 加群を全 Hom end ごと使い、標準演算の閉性を証明する。
規約：冪等完備性は別工程。使われ方：β5 の Perf(A) の模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 射影的 perfect 加群の実 dg nerve による Perf の模型。 -/
abbrev dgModulePerfectInfinityCategory := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R D)
/-- 既存の射影的 perfect 条件は、実零・標準 cone・fiber で閉じる。 -/
lemma dgModulePerfectProperty_closed :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleClosedProperty R D (modulePerfectProjectiveOver R D Set.univ) where
  zero := _root_.SerrePositivity.DifferentialGraded.modulePerfectProjectiveOver_zero R D Set.univ
  cone f hM hN := _root_.SerrePositivity.DifferentialGraded.modulePerfectProjectiveOver_cone R D hM hN f
  fiber f hM hN := _root_.SerrePositivity.DifferentialGraded.modulePerfectProjectiveOver_shift R D
    (_root_.SerrePositivity.DifferentialGraded.modulePerfectProjectiveOver_cone R D hM hN f) (-1)
/-- Perf の実 dg nerve は安定。 -/
theorem dgModulePerfectInfinityCategory_isStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgModulePerfectInfinityCategory R D) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModule_isStable R D _ (dgModulePerfectProperty_closed R D)
/-- 実 perfect 加群から全射影的加群への、同じ全 Hom end の dg 包含。 -/
def dgPerfectToProjective : DGFunctor R (PerfectDGModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullFunctorRestriction R (RightModule R D) (RightModule R D)
    (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R D)) _ _ (fun _ h => h.1)
/-- 実 perfect 加群から射影的模型への dg 包含の nerve は完全。 -/
lemma dgPerfectToProjectiveNerve_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectToProjective R D)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleFunctorNerve_isExactFunctor R D D (DGFunctor.id (RightModule R D)) _ _
    (dgModulePerfectProperty_closed R D) (fun _ h => h.1)
/-- Perf から半自由模型の D(D) への実 ∞ 関手。 -/
def dgPerfectInclusionInfinity : dgModulePerfectInfinityCategory R D ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectToProjective R D) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.inv
/-- Perf の実 ∞ 関手は完全。 -/
theorem dgPerfectInclusionInfinity_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgPerfectInclusionInfinity R D) := by
  let := dgPerfectToProjectiveNerve_isExactFunctor R D
  have hi := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.symm.isQCatEquivalence
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.inv at hi
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _
/-- Perf の実 ∞ 関手は、全写像空間で充満忠実。 -/
theorem dgPerfectInclusionInfinity_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgPerfectInclusionInfinity R D) := by
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectToProjective R D)) := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_homIso
    intro M N
    change IsIso (𝟙 (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M.val N.val))
    infer_instance
  have hi := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.symm.isQCatEquivalence
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.inv at hi
  exact hg.comp hi.isFullyFaithful
end SerrePositivity.InfinityCategories.Project.DerivedCategories
