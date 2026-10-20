module
public import SerrePositivity.InfinityCategories.Derived.DGAlgebraDerivedInfinity
public import SerrePositivity.InfinityCategories.Derived.DGPerfectModulesInfinity
/-!
概要：非可換 dg 代数の Perf の安定 ∞ 圏と D(A) への実完全充満包含。
方針：同じ一対象 dg 圏上の射影的 perfect 加群を使う。
規約：冪等完備性は別工程。使われ方：β5 の Perf(A) の対象の供給。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (B : Mon (Complex R))
/-- 非可換 dg 代数の射影的 perfect 加群の実 nerve。 -/
abbrev dgAlgebraPerfectInfinityCategory :=
  dgModulePerfectInfinityCategory R (dgAlgebraCategory R B)
/-- 非可換 dg 代数の Perf は実安定 ∞ 圏。 -/
theorem dgAlgebraPerfectInfinityCategory_isStable :
    IsStable (dgAlgebraPerfectInfinityCategory R B) :=
  dgModulePerfectInfinityCategory_isStable R (dgAlgebraCategory R B)
/-- 非可換 dg 代数の Perf から D(A) への実 ∞ 関手。 -/
abbrev dgAlgebraPerfectInclusionInfinity := dgPerfectInclusionInfinity R (dgAlgebraCategory R B)
/-- Perf から D(A) への実 ∞ 関手は完全。 -/
theorem dgAlgebraPerfectInclusionInfinity_isExactFunctor :
    IsExactFunctor (dgAlgebraPerfectInclusionInfinity R B) :=
  dgPerfectInclusionInfinity_isExactFunctor R (dgAlgebraCategory R B)
/-- Perf から D(A) への実 ∞ 関手は全写像空間で充満忠実。 -/
theorem dgAlgebraPerfectInclusionInfinity_isFullyFaithful :
    IsFullyFaithful (dgAlgebraPerfectInclusionInfinity R B) :=
  dgPerfectInclusionInfinity_isFullyFaithful R (dgAlgebraCategory R B)
end SerrePositivity.InfinityCategories
