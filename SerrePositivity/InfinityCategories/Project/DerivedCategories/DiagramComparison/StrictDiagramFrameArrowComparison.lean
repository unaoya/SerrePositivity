module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFrameArrowLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeLimits

/-!
概要：Hom要素圏上の元の錐から、指定したBousfield–Kan比較射を作る。
方針：既存の重み付き錐比較を使い、全射での評価が元の脚を回収することを証明する。
規約：このファイルでは比較射の弱同値性を仮定も主張もしない。
使われ方：HTT 4.2.4.4のRR02(a)、導来end比較の実射の固定。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
  (X Y : StrictComplexDiagram A d)

/-- 同じ二変数係数をHom要素圏上のKan図式として束ねる。 -/
def strictDiagramFrameArrowKanDiagram :=
  strictDiagramArrowElementsBase d ⋙ strictDiagramEvaluatedValueKan A d X Y

/-- 元の錐の頂点のKan性を束ねた、同じ脚を持つ錐。 -/
def strictDiagramFrameArrowKanCone : Cone (strictDiagramFrameArrowKanDiagram A d X Y) :=
  kanObjectConeOfUnderlying _ (strictDiagramFrameArrowCone A d X Y)
    (strictDiagramFrameMapping_kanComplex A d X Y)

/-- Kan図式の錐を忘れると、元の全単体的な錐に一致する。 -/
lemma strictDiagramFrameArrowKanCone_forget :
    kanObjectForget.mapCone (strictDiagramFrameArrowKanCone A d X Y) =
      strictDiagramFrameArrowCone A d X Y := rfl

/-- 同じKan図式の錐の通常の極限性。 -/
def strictDiagramFrameArrowKanIsLimit : IsLimit (strictDiagramFrameArrowKanCone A d X Y) :=
  kanObjectCone_isLimit_of_forget _ (strictDiagramFrameArrowIsLimit A d X Y)

/-- 元のframe Homから同じ係数のBousfield–Kan endへの標準比較射。 -/
def strictDiagramFrameArrowComparison : strictDiagramFrameMapping A d X Y ⟶
    bousfieldKanHolim (strictDiagramFrameArrowDiagram A d X Y) :=
  bousfieldKanConeComparison (strictDiagramFrameArrowCone A d X Y)

/-- 標準比較は全ての添字射で元の脚を回収する。 -/
lemma strictDiagramFrameArrowComparison_evaluation (t : StrictDiagramArrowElements.{u} d) :
    strictDiagramFrameArrowComparison A d X Y ≫
      bousfieldKanEvaluation (strictDiagramFrameArrowDiagram A d X Y) t =
        strictDiagramFrameArrowLeg A d X Y t :=
  weightedConeComparison_eval _ (strictDiagramFrameArrowCone A d X Y) t _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
