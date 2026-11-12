module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictDiagramEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.InfinityCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.NerveInclusion
import all SerrePositivity.InfinityCategories.Project.DerivedCategories.InfinityCategory
import all SerrePositivity.InfinityCategories.Project.DerivedCategories.NerveInclusion

/-!
# 半自由複体の strict 図式の全評価

## 概要
半自由複体の閉零圏を値に持つ strict 図式を、既存 D(A) の全図式として読む。

## 方針
図式圏の全 nerve と添字の nerve を同時に評価し、閉零圏の dg nerve 包含を合成する。

## 規約
半自由対象の間の射は閉零圏で扱う。頂点・辺だけの選択へ切り下げない。

## 使われ方
HTT 4.2.4.1・A.3.3、HA 1.2.4。Δᵒᵖ の実現余錐の全パラメーターの図式側。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet MonoidalCategory SerrePositivity.DifferentialGraded
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 半自由複体を値に持つ strict 図式の通常圏。 -/
abbrev StrictSemifreeDiagram := J ⥤ ClosedCategory A (Semifree A)

/-- 一つの strict 図式の全射列を、既存 D(A) の図式へ送る。 -/
def strictSemifreeDiagram (F : StrictSemifreeDiagram A J) :
    (SSet.uliftFunctor.{u + 1, 0}).obj (nerve J) ⟶ derivedInfinityCategory A :=
  strictDiagramNerve J (ClosedCategory A (Semifree A)) F ≫
    closedNerveInclusion A (Semifree A)

/-- strict 図式の全パラメーターと添字を同時に動かす、既存 D(A) 値の評価。 -/
def strictSemifreeEvaluation :
    nerve (StrictSemifreeDiagram A J) ⊗ (SSet.uliftFunctor.{u + 1, 0}).obj (nerve J) ⟶
      derivedInfinityCategory A :=
  strictDiagramEvaluation J (ClosedCategory A (Semifree A)) ≫
    closedNerveInclusion A (Semifree A)

/-- 一つの図式の頂点は、元の半自由複体そのもの。 -/
theorem strictSemifreeDiagram_vertex (F : StrictSemifreeDiagram A J) (j : J) :
    derivedInfinityCategoryVertexEquiv A
      ((strictSemifreeDiagram A J F).app (Opposite.op ⦋0⦌)
        (ULift.up (ComposableArrows.mk₀ j))) =
      ForgetEnrichment.to (Complex A) (F.obj j) := by
  change ForgetEnrichment.to (Complex A)
    (nerveEquiv ((strictDiagramNerve J (ClosedCategory A (Semifree A)) F).app (Opposite.op ⦋0⦌)
      (ULift.up (ComposableArrows.mk₀ j)))) = _
  rw [strictDiagramNerve_obj]
  rfl

/-- 全評価でも、同じパラメーターの同じ頂点を保持する。 -/
theorem strictSemifreeEvaluation_vertex (F : StrictSemifreeDiagram A J) (j : J) :
    derivedInfinityCategoryVertexEquiv A
      ((strictSemifreeEvaluation A J).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ F, ULift.up (ComposableArrows.mk₀ j))) =
      ForgetEnrichment.to (Complex A) (F.obj j) := by
  change ForgetEnrichment.to (Complex A)
    (nerveEquiv ((strictDiagramEvaluation J (ClosedCategory A (Semifree A))).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ F, ULift.up (ComposableArrows.mk₀ j)))) = _
  rw [strictDiagramEvaluation_obj]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
