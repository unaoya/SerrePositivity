module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGStableHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveUniverseLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGAlgebraPerfectInfinity
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletenessUniverse
public import Mathlib.CategoryTheory.Idempotents.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectIdempotentCompleteGeneral
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
universe b c
variable (R : Type b) [CommRing R]
variable (D : Type c) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{b} D]
/-- 任意の小 dg 圏の実 Perf は coherent な意味で冪等完備。 -/
lemma dgModulePerfectInfinityCategory_isIdempotentComplete :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R D) :=
  _root_.SerrePositivity.InfinityCategories.HA.Section1_2_4.dgNerve_isIdempotentComplete_of_h0 R (PerfectDGModule R D)
/-- 非可換 dg 代数の実 Perf は coherent な意味で冪等完備。 -/
lemma dgAlgebraPerfectInfinityCategory_isIdempotentComplete (B : Mon (_root_.SerrePositivity.DifferentialGraded.Complex R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPerfectInfinityCategory R B) :=
  dgModulePerfectInfinityCategory_isIdempotentComplete R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
