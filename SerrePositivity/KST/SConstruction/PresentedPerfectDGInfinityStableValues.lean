module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInfinityFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGComparison

/-! # 厳密豊穣 Perf 関手の実安定値と元の Perf との比較
概要：Cat∞ 値 Perf 関手の各実値は安定であり、元の実 Perf native nerve と評価で同値。
方針：同じラベル付き模型の既存評価同値と安定性を、そのまま実値に回収する。
規約：射の完全性や K の関手性はこの値の比較だけからは主張しない。
使われ方：完全関手空間から S•・BF K への豊穣作用の入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の厳密豊穣 Perf 関手の実 QCat 値は、同じ元の評価同値により安定。 -/
lemma presentedPerfectDGQCat_isStable (C : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (presentedPerfectDGQCat A C).obj :=
  presentedPerfectDGNerve_isStable A C

/-- 元の実 QCat 値から元の実 Perf native nerve への、同じ評価による実同値。 -/
def presentedPerfectDGQCatEvaluationEquivalence (C : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (presentedPerfectDGQCat A C).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PerfectDGModule A C)) :=
  presentedPerfectDGNerveEquivalence A C

/-- 元の厳密豊穣 Perf 関手の値を、同じ安定な K 入力として保持する。 -/
def presentedPerfectDGEnrichedStableValue (C : PerfDGInput.{u, v} A) :
    StableModel.{max (u + 1) v} where
  carrier := (presentedPerfectDGQCat A C).obj
  quasicategory := inferInstance
  stable := presentedPerfectDGQCat_isStable A C

/-- 元の安定値の底は、同じ実 QCat 値の全 native 単体集合。 -/
lemma presentedPerfectDGEnrichedStableValue_carrier (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGEnrichedStableValue A C).carrier = (presentedPerfectDGQCat A C).obj := rfl

end SerrePositivity.KST.SConstruction
