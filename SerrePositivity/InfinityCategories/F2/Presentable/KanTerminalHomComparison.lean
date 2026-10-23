module

public import SerrePositivity.InfinityCategories.F2.Presentable.KanTerminalEnriched
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallKanHomContinuity
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorEnrichedEvaluation
public import SerrePositivity.InfinityCategories.F1.LeftFibrationCoherentEvaluation

/-!
概要：終対象上の相対 Hom の全豊穣評価を、元の Kan 内部 Hom の全豊穣評価へ戻す。
方針：全関手空間の厳密な相対同型を成分とし、全高次射への作用と整合する比較を構成する。
規約：同じ比較から coherent nerve の全自然同型を回収し、値ごとの選択をしない。
使われ方：N の compact 定義の全共変 Hom と、小さい Kan 全 Hom との宇宙比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 同じ Kan 始点の終対象上の相対 Hom を、全 Kan 変数で同時に評価する。 -/
def kanTerminalHomEvaluation (K : KanObject.{u}) :
    EnrichedFunctor SSet.{u} KanObject.{u} KanObject.{u} :=
  kanTerminalEnriched.comp SSet (relativeFunctorEnrichedEvaluation (kanTerminalObject K).val)

/-- 元の相対 Hom の包含は、全高次射の作用に関しても元の内部 Hom へ整合する。 -/
def kanTerminalHomEnrichedComparison (K : KanObject.{u}) :
    KanEnrichedComparison (kanTerminalHomEvaluation K) (kanInternalHomEnriched K) := by
  refine ⟨fun L ↦ (terminalRelativeHomIso K.obj L.obj).hom, ?_⟩
  intro L M
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, f⟩
  apply Functor.HomObj.ext
  funext m α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 同じ全比較を coherent nerve に移し、元の小さい Hom 全関手の自然同型を得る。 -/
def kanTerminalHomInfinityComparisonIso (K : KanObject.{u}) :
    FunctorIso (kanTerminalInfinity ≫ leftFibrationCoherentEvaluation (kanTerminalObject K).val)
      (kanInternalHomInfinity K) := by
  have e := kanEnrichedComparisonIso (kanTerminalHomEnrichedComparison K)
    (fun L ↦ (qCatEquivalenceOfIso (terminalRelativeHomIso K.obj L.obj)).isQCatEquivalence)
  simpa only [kanTerminalHomEvaluation, coherentNerveMap_comp,
    kanTerminalInfinity, kanInternalHomInfinity, leftFibrationCoherentEvaluation] using e

end SerrePositivity.InfinityCategories.F2.Presentable
