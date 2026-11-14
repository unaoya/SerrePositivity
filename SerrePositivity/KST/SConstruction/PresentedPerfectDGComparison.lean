module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGModel
public import SerrePositivity.KST.SConstruction.SmallDGInput
public import SerrePositivity.KST.SConstruction.DGKQuasiEquivalence

/-! # ラベル付き Perf 模型と元の実 Perf の比較
概要：小さい入力の dg 表示と各代表から、元の実 Perf への評価準同値を証明する。
方針：入力の小さい dg 表示とその Perf 延長を通して、既存の小さい代表を使う。
規約：入力は任意の Small.{u} D。対象・nerve の宇宙を区別する。使われ方：関手的 Perf の K 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]
section SameUniverse
variable (D : Type u) [DGCategory A D]

/-- 各小さい代表を、恒等入力のラベルを保持して模型へ入れる。 -/
def presentedPerfectDGSeed (X : SmallPerfectDGModuleOver A D Set.univ) :
    PresentedPerfectDGObject A D where
  source := D
  enrichment := inferInstance
  seed := X
  arrow := DGFunctor.id D

/-- 恒等ラベルの評価は、元の実延長の単位同型で同じ代表を回収する。 -/
def presentedPerfectDGSeedIso (X : SmallPerfectDGModuleOver A D Set.univ) :
    ForgetEnrichment.of (Complex A)
        (presentedPerfectDGValue A D (presentedPerfectDGSeed A D X)) ≅
      ForgetEnrichment.of (Complex A) X.val :=
  perfectDGExtensionIdentityAt A D X.val

end SameUniverse
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 一つの小さい出発圏からの Perf 延長が本質的全射なら、ラベル評価も本質的全射。 -/
lemma presentedPerfectDGEvaluationEssSurj_of_extension
    (C : Type u) [DGCategory A C] (F : DGFunctor A C D)
    [(perfectDGExtension A C D F).onHomotopy.EssSurj] :
    (presentedPerfectDGEvaluation A D).onHomotopy.EssSurj where
  mem_essImage X := by
    let L := (smallPerfectDGModuleInclusion A C Set.univ).onHomotopy ⋙
      (perfectDGExtension A C D F).onHomotopy
    obtain ⟨Z, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage L X
    let Z' := ForgetEnrichment.to (Complex A) Z.as
    let W : PresentedPerfectDGObject A D :=
      { source := C, enrichment := inferInstance, seed := Z', arrow := F }
    refine ⟨(toHomotopy A (PresentedPerfectDGObject A D)).obj
      (ForgetEnrichment.of (Complex A) W), ⟨?_⟩⟩
    exact e

/-- 評価は H⁰ で本質的全射。小さい入力表示の Perf 延長と代表の全射性を合成する。 -/
instance presentedPerfectDGEvaluationHomotopyEssSurj :
    (presentedPerfectDGEvaluation A D).onHomotopy.EssSurj := by
  have hF := perfectDGExtension_quasiEquivalence_of_quasiEquivalence A (SmallDGInput A D) D
    (smallDGInputEvaluation A D) (smallDGInputEvaluation_quasiEquivalence A D)
  let := hF.2
  exact presentedPerfectDGEvaluationEssSurj_of_extension A D
    (SmallDGInput A D) (smallDGInputEvaluation A D)

/-- 評価は全 Hom で恒等、H⁰ で本質的全射な実 dg 準同値。 -/
lemma presentedPerfectDGEvaluation_quasiEquivalence :
    QuasiEquivalence (presentedPerfectDGEvaluation A D) :=
  ⟨presentedPerfectDGEvaluation_quasiIso A D, inferInstance⟩

/-- ラベルを保持する模型の native dg nerve と、元の実 Perf の nerve の同値。 -/
def presentedPerfectDGNerveEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PerfectDGModule A D)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.dgQuasiEquivalenceNerveEquivalence (presentedPerfectDGEvaluation A D)
    (presentedPerfectDGEvaluation_quasiEquivalence A D)

/-- ラベル付き Perf の native nerve は、実際の評価同値で安定性を反映する。 -/
lemma presentedPerfectDGNerve_isStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D)) :=
  (presentedPerfectDGNerveEquivalence A D).isStable_iff.mpr
    (perfectDGStableModel A D Set.univ).stable

/-- 元の全 Hom 複体を持つラベル付き Perf の実安定模型。 -/
def presentedPerfectDGStableModel : StableModel.{max (u + 1) v} where
  carrier := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D)
  quasicategory := inferInstance
  stable := presentedPerfectDGNerve_isStable A D

end SerrePositivity.KST.SConstruction
