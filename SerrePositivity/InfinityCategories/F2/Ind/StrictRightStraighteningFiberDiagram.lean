module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationOppositeDiagram
public import SerrePositivity.InfinityCategories.F1.Fibrations.RightStraighteningInfinityEquivalence
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningAllBasesEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanConeLimits

/-!
概要：strict な right straightening 図式の評価は、同じ反転した fiber の図式と関手同型。
方針：共通 Hom 解像上の大域比較と、元の left straightening の評価同型を合成する。
規約：全図式の関手同型。頂点ごとの比較だけで代用しない。
使われ方：strict な right fibration 余錐から前層側の点ごとの余極限比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {B : SSet.{u}} {I : Type u} [SmallCategory I]

/-- 豊穣な fiber 評価の通常の作用は元の底上の射が誘導する同じ fiber 写像。 -/
lemma leftFiberEvaluation_underlying_map {C : SSet.{u}} (b : C _⦋0⦌)
    {p q : LeftFibrationObject C} (f : p ⟶ q) :
    (coherentEnrichedUnderlyingFunctor (leftFibrationFiberEvaluationEnriched b)).map f =
      vertexFiberMap p.val.hom q.val.hom f.left (Over.w f) b := by
  apply functorVertex_injective
  have h := coherentEnrichedUnderlyingFunctor_vertex (leftFibrationFiberEvaluationEnriched b) f
  change functorVertex _ = (relativeFunctorFiberHom p.val.hom q.val.hom b).app _
    (relativeFunctorVertex q.val.hom p.val.hom f.left (Over.w f)) at h
  exact h.trans (relativeFunctorFiberHom_vertex _ _ _ _ _)

/-- 同じ通常の right fibration 図式を反転した、実際の Kan fiber 図式。 -/
def rightFibrationOppositeFiberDiagram (F : I ⥤ RightFibrationObject B) (b : B.op _⦋0⦌) :
    I ⥤ KanObject.{u} :=
  (F ⋙ rightFibrationOppositeOrdinary B) ⋙
    coherentEnrichedUnderlyingFunctor (leftFibrationFiberEvaluationEnriched b)

/-- 反転した図式の coherent な fiber 評価は同じ通常の Kan 図式の coherent 表示。 -/
lemma rightFibrationOppositeFiberDiagram_coherent (F : I ⥤ RightFibrationObject B)
    (b : B.op _⦋0⦌) :
    strictCoherentDiagram (F ⋙ rightFibrationOppositeOrdinary B) ≫
      leftFibrationInfinityFiberEvaluation b =
        kanDiagramCoherentNerve (rightFibrationOppositeFiberDiagram F b) := by
  rw [leftFibrationInfinityFiberEvaluation, strictCoherentDiagram_postcomp]
  exact strictCoherentDiagram_eq_kanDiagram _

/-- 元の right straightening の全評価図式は、同じ実際の反転 fiber 図式と関手同型。 -/
def strictRightStraighteningFiberDiagramIso (F : I ⥤ RightFibrationObject B)
    (b : B.op _⦋0⦌) :
    FunctorIso
      (strictCoherentDiagram F ≫ rightStraighteningInfinityMap B ≫
        evaluateFunctorAt (ULift.up b))
      (kanDiagramCoherentNerve (rightFibrationOppositeFiberDiagram F b)) := by
  have eo := (strictRightFibrationOppositeDiagramIso F).postcomp
    (leftStraighteningInfinityMap B.op ≫ evaluateFunctorAt (ULift.up b))
  have ef := (leftStraighteningInfinityMap_evaluateIso b).precomp
    (strictCoherentDiagram (F ⋙ rightFibrationOppositeOrdinary B))
  have eh := rightFibrationOppositeFiberDiagram_coherent F b
  exact eo ≪≫ ef ≪≫ eqToIso
    (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) eh)

end SerrePositivity.InfinityCategories.F2.Ind
