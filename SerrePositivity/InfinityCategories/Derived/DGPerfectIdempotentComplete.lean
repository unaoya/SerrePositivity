module
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletenessEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGNerveUniverseLift
public import SerrePositivity.InfinityCategories.Derived.DGAlgebraPerfectInfinity
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration
public import SerrePositivity.InfinityCategories.F2.Idempotent.Completion
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletenessUniverse
public import Mathlib.CategoryTheory.Idempotents.Basic
public import SerrePositivity.InfinityCategories.Derived.DGPerfectIdempotentCompleteGeneral
/-!
概要：実 Perf の coherent 冪等完備性と、H⁰ 分裂から dg nerve への一般判定。
方針：充満忠実像の retract と Yoneda 冪等完備化、対象宇宙持ち上げを接続する。
規約：元の全 Idem 図式を厳密に回収する強い分裂を結論とする。
使われ方：β5(f)、非可換 dg 代数の Perf(A) の Cat^perf への供給。
-/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
universe b c
variable (R : Type b) [CommRing R]
variable (D : Type c) [DGCategory R D] [Small.{b} D]
/-- 任意の小 dg 圏の実 Perf は coherent な意味で冪等完備。 -/
lemma dgModulePerfectInfinityCategory_isIdempotentComplete :
    F2.Idempotent.IsIdempotentComplete (dgModulePerfectInfinityCategory R D) :=
  dgNerve_isIdempotentComplete_of_h0 R (PerfectDGModule R D)
/-- 非可換 dg 代数の実 Perf は coherent な意味で冪等完備。 -/
lemma dgAlgebraPerfectInfinityCategory_isIdempotentComplete (B : Mon (Complex R)) :
    F2.Idempotent.IsIdempotentComplete (dgAlgebraPerfectInfinityCategory R B) :=
  dgModulePerfectInfinityCategory_isIdempotentComplete R (dgAlgebraCategory R B)
end SerrePositivity.InfinityCategories
