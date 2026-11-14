module
public import SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraDerivedInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectModulesInfinity
/-!
概要：非可換 dg 代数の Perf の安定 ∞ 圏と D(A) への実完全充満包含。
方針：同じ一対象 dg 圏上の射影的 perfect 加群を使う。
規約：冪等完備性は別工程。使われ方：β5 の Perf(A) の対象の供給。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (B : Mon (Complex R))
/-- 非可換 dg 代数の射影的 perfect 加群の実 nerve。 -/
abbrev dgAlgebraPerfectInfinityCategory :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)
/-- 非可換 dg 代数の Perf は実安定 ∞ 圏。 -/
theorem dgAlgebraPerfectInfinityCategory_isStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgAlgebraPerfectInfinityCategory R B) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory_isStable R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)
/-- 非可換 dg 代数の Perf から D(A) への実 ∞ 関手。 -/
abbrev dgAlgebraPerfectInclusionInfinity := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)
/-- Perf から D(A) への実 ∞ 関手は完全。 -/
theorem dgAlgebraPerfectInclusionInfinity_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgAlgebraPerfectInclusionInfinity R B) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity_isExactFunctor R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)
/-- Perf から D(A) への実 ∞ 関手は全写像空間で充満忠実。 -/
theorem dgAlgebraPerfectInclusionInfinity_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgAlgebraPerfectInclusionInfinity R B) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity_isFullyFaithful R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
