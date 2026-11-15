module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SemifreePointComparison
public import SerrePositivity.EInfinity.ComplexLimits.SemifreeRingEvaluation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.DGQuasiEquivalenceNerve

/-!
概要：既存の一点半自由dg加群の評価は、既存の半自由複体模型との準同値。
方針：全Homの既存評価同型と、定数一点加群による同じ半自由対象の復元を使う。
規約：IS-W2 C02の既存係数移送則。分解関手や導来圏の模型を取り換えない。
使われ方：HA 1.2.4、同じTot錐の出力分解後の極限性の輸送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]

/-- 既存の一点半自由加群評価は、各HomとH⁰の対象を同じ模型で比較する準同値。 -/
theorem semifreeRingEvaluationDG_quasiEquivalence :
    QuasiEquivalence (semifreeRingEvaluationDG A) :=
  SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.semifreePointEvaluation_quasiEquivalence A

/-- 既存の半自由一点評価の∞関手は、同じ既存D(A)への同値。 -/
theorem semifreeRingEvaluationInfinity_isQCatEquivalence :
    IsQCatEquivalence (semifreeRingEvaluationInfinity A) :=
  dgNerve_map_isQCatEquivalence_of_quasiEquivalence
    (semifreeRingEvaluationDG A) (semifreeRingEvaluationDG_quasiEquivalence A)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
