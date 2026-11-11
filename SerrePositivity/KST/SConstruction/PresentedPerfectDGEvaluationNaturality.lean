module
public import SerrePositivity.KST.SConstruction.DGStandardFunctorIsoReflection
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGActionExact
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFEvaluationComparison
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFRealizationInvariance

/-! # 元の実 Perf 評価の native 関手同型による入力自然性
概要：元の評価と実延長の四角形は、同じ native dg nerve 射の関手同型で可換。
方針：既存の全 Hom 閉零比較から得た標準 DK 同型を、元の比較同値で戻す。
規約：元の実入力射・評価射を変更しない。使われ方：元の dgK への整数 π 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の実 Perf 評価四角形の native dg nerve 上の同じ関手同型。 -/
def presentedPerfectDGEvaluationNativeComparison (D E : Type v)
    [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
    (F : DGFunctor A D E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation A D) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension A D E F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A D E F) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation A E)) := by
  have h := dgStandardFunctorIso_to_native (presentedPerfectDGStandardActionComparisonIso A D E F)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at h
  exact h

/-- 同じ安定入力の評価と元の入力作用の四角形は、元の native 関手同型で可換。 -/
def presentedPerfectDGBFEvaluationInputComparison
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (((presentedPerfectDGBFEvaluationEquivalence A X).hom ≫
        perfectDGStableMap A X Y f.down).val)
      ((presentedPerfectDGBFInputStableMap A f ≫
        (presentedPerfectDGBFEvaluationEquivalence A Y).hom).val) :=
  presentedPerfectDGEvaluationNativeComparison A X Y f.down

end SerrePositivity.KST.SConstruction
