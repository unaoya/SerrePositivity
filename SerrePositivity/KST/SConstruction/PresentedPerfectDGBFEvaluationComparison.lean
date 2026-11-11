module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEvaluationExact
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGExactValues
public import SerrePositivity.KST.SConstruction.MultiSExactEnrichedFunctor
public import SerrePositivity.KST.SConstruction.DGKTheory

/-! # 同じラベル付き Perf の旧 BF K と元の dgK の比較
概要：実 Perf 評価を保持する旧 BF K 射は、元の dgK への全整数 π 同型。
方針：既存の実 dg nerve 評価同値を完全な安定入力の同値へ束ねる。
規約：新 BF 列との比較の完成は別工程。使われ方：元の dgK 比較の評価側。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Spectra
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の実 Perf 評価を順方向に保持する、同じ安定入力の完全な同値。 -/
def presentedPerfectDGBFEvaluationEquivalence (C : PerfDGInput.{u, v} A) :
    StableModelEquivalence
      (stableCategoryModel (presentedPerfectDGStableCategory A C))
      (perfectDGStableModel A C Set.univ) := by
  let e := presentedPerfectDGNerveEquivalence A C
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact ⟨presentedPerfectDGEvaluationStableMap A C,
    ⟨e.inv, preservesCofiberData_of_isExactFunctor e.inv⟩, e.homInvIso, e.invHomIso⟩

/-- 同じ完全同値の順方向は元の実 dg 評価の native nerve。 -/
lemma presentedPerfectDGBFEvaluationEquivalence_hom (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFEvaluationEquivalence A C).hom.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation A C) := rfl

/-- 同じラベル付き Perf の旧実 BF K から、元の dgK への実評価射。 -/
def presentedPerfectDGBFEvaluationKMap (C : PerfDGInput.{u, v} A) :
    kOmegaSpectrum (stableCategoryModel (presentedPerfectDGStableCategory A C)) ⟶ dgK A C :=
  kSpectrumMap (presentedPerfectDGBFEvaluationEquivalence A C).hom

/-- 元の評価による同じ旧 BF K 射は、全整数次数で π 同型。 -/
lemma presentedPerfectDGBFEvaluationKMap_piIsomorphism (C : PerfDGInput.{u, v} A) :
    OmegaSpectrum.PiIsomorphism (presentedPerfectDGBFEvaluationKMap A C) :=
  kSpectrumMap_piIsomorphism_of_equivalence (presentedPerfectDGBFEvaluationEquivalence A C)

end SerrePositivity.KST.SConstruction
