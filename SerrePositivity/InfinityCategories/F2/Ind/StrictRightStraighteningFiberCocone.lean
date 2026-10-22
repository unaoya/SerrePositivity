module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationOppositeCocone
public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightStraighteningCocone
public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationOppositeFiber

/-!
概要：元の right straightening 余錐全体の評価と、同じ実際の反転 fiber 余錐の関手同型。
方針：反転比較を余錐全体へ延長し、元の straightening の評価同型と後合成の等式を合成する。
規約：全 join 射の関手同型。別の余錐や頂点だけの同値で代用しない。
使われ方：指定された同じ前層余錐の余極限性を各点で検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {B : SSet.{u}} {I : Type u} [SmallCategory I] {F : I ⥤ RightFibrationObject B}

/-- 元の余錐を反転し、同じ実際の fiber を各脚で取る Kan 余錐。 -/
def rightFibrationOppositeFiberCocone (c : Cocone F) (b : B.op _⦋0⦌) :
    Cocone (rightFibrationOppositeFiberDiagram F b) :=
  (coherentEnrichedUnderlyingFunctor (leftFibrationFiberEvaluationEnriched b)).mapCocone
    ((rightFibrationOppositeOrdinary B).mapCocone c)

/-- 同じ反転余錐の fiber 評価は、同じ Kan 余錐の全 join 射。 -/
lemma rightFibrationOppositeFiberCocone_coherent (c : Cocone F) (b : B.op _⦋0⦌) :
    (strictNativeCocone ((rightFibrationOppositeOrdinary B).mapCocone c)).val ≫
      leftFibrationInfinityFiberEvaluation b =
        (strictNativeCocone (rightFibrationOppositeFiberCocone c b)).val :=
  strictNativeCocone_postcomp_val _ (leftFibrationFiberEvaluationEnriched b)

/-- 元の right straightening の評価余錐全体は、同じ反転 fiber 余錐と関手同型。 -/
def strictRightStraighteningFiberCoconeIso (c : Cocone F) (b : B.op _⦋0⦌) :
    FunctorIso
      ((strictNativeCocone c).val ≫ rightStraighteningInfinityMap B ≫
        evaluateFunctorAt (ULift.up b))
      (strictNativeCocone (rightFibrationOppositeFiberCocone c b)).val := by
  have eo := (strictRightFibrationOppositeCoconeIso c).postcomp
    (leftStraighteningInfinityMap B.op ≫ evaluateFunctorAt (ULift.up b))
  have ef := (leftStraighteningInfinityMap_evaluateIso b).precomp
    (strictNativeCocone ((rightFibrationOppositeOrdinary B).mapCocone c)).val
  have eh := rightFibrationOppositeFiberCocone_coherent c b
  exact eo ≪≫ ef ≪≫ eqToIso
    (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) eh)

/-- 指定した同じ strict 余極限の前層余錐を評価した全 join 射の比較。 -/
def strictRightStraighteningColimitFiberCoconeIso [IsFiltered I]
    (F : I ⥤ RightFibrationObject B) (b : B.op _⦋0⦌) :
    FunctorIso
      ((strictRightStraighteningCocone F).val ≫ evaluateFunctorAt (ULift.up b))
      (strictNativeCocone
        (rightFibrationOppositeFiberCocone (strictRightFibrationColimitCocone F) b)).val :=
  strictRightStraighteningFiberCoconeIso _ _

end SerrePositivity.InfinityCategories.F2.Ind
