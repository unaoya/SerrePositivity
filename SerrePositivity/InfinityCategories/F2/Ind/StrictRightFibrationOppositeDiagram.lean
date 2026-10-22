module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationOpposite
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeFunctorImage

/-!
概要：strict な right fibration 図式の実際の反転は、元の反転図式と大域的に関手同型。
方針：標準の共通 Hom 解像への持ち上げと、同じ比較同値の関手同型を前後合成する。
規約：元の全図式を保持し、頂点ごとの同型だけで代用しない。
使われ方：right straightening の strict 図式上の fiber 評価比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {B : SSet.{u}} {I : Type u} [SmallCategory I]

/-- 同じ通常の図式の定値 Hom による共通解像への標準持ち上げ。 -/
def rightFibrationCommonDiagram (F : I ⥤ RightFibrationObject B) :
    I ⥤ EdgewiseEnrichedObject (RightFibrationObject B) :=
  F ⋙ edgewiseOrdinaryLift (RightFibrationObject B)

/-- 同じ共通図式の右脚は元の通常の図式。 -/
lemma rightFibrationCommonDiagram_right (F : I ⥤ RightFibrationObject B) :
    rightFibrationCommonDiagram F ⋙
      coherentEnrichedUnderlyingFunctor (edgewiseEnrichedRight (RightFibrationObject B)) = F := by
  rw [rightFibrationCommonDiagram, Functor.assoc, edgewiseOrdinaryLift_right, Functor.comp_id]

/-- 同じ共通図式の反転脚は元の通常の反転図式。 -/
lemma rightFibrationCommonDiagram_opposite (F : I ⥤ RightFibrationObject B) :
    rightFibrationCommonDiagram F ⋙
      coherentEnrichedUnderlyingFunctor (rightFibrationOppositeEnriched B) =
        F ⋙ rightFibrationOppositeOrdinary B := by
  rw [rightFibrationCommonDiagram, Functor.assoc, edgewiseOrdinaryLift_rightFibrationOpposite]

/-- 共通図式の右射影の coherent な表示は元の同じ図式。 -/
lemma rightFibrationCommonDiagram_coherentRight (F : I ⥤ RightFibrationObject B) :
    strictCoherentDiagram (rightFibrationCommonDiagram F) ≫
      (edgewiseEnrichedInfinityEquivalence (RightFibrationObject B)).hom =
        strictCoherentDiagram F := by
  change _ ≫ coherentNerveMap (edgewiseEnrichedRight (RightFibrationObject B)) = _
  rw [strictCoherentDiagram_postcomp, rightFibrationCommonDiagram_right]

/-- 元の strict 図式への実際の反転は、同じ通常の反転図式に全パラメーターで関手同型。 -/
def strictRightFibrationOppositeDiagramIso (F : I ⥤ RightFibrationObject B) :
    FunctorIso (strictCoherentDiagram F ≫ rightFibrationOppositeInfinityMap B)
      (strictCoherentDiagram (F ⋙ rightFibrationOppositeOrdinary B)) := by
  let E := edgewiseEnrichedInfinityEquivalence (RightFibrationObject B)
  let R := strictCoherentDiagram (rightFibrationCommonDiagram F)
  let O := coherentNerveMap (rightFibrationOppositeEnriched B)
  have he := (E.homInvIso.precomp R).postcomp O
  change FunctorIso ((R ≫ E.hom) ≫ (E.inv ≫ O)) (R ≫ O) at he
  have hr : R ≫ E.hom = strictCoherentDiagram F :=
    rightFibrationCommonDiagram_coherentRight F
  have ho : R ≫ O = strictCoherentDiagram (F ⋙ rightFibrationOppositeOrdinary B) := by
    rw [strictCoherentDiagram_postcomp, rightFibrationCommonDiagram_opposite]
  rw [hr, ho] at he
  exact he

end SerrePositivity.InfinityCategories.F2.Ind
