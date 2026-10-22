module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictCoconePostcomposition
public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationOppositeDiagram

/-!
概要：元の right fibration 余錐全体の実際の反転と、同じ通常の反転余錐の関手同型。
方針：標準の共通 Hom 解像の余錐に同じ比較同値の二胞体を前後合成する。
規約：全 join 射の関手同型。別の余錐の存在で代用しない。
使われ方：元の right straightening 余錐の点ごとの余極限性の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {B : SSet.{u}} {I : Type u} [SmallCategory I] {F : I ⥤ RightFibrationObject B}

/-- 元の通常の余錐の全ての射を定値 Hom で共通解像へ持ち上げる。 -/
def rightFibrationCommonCocone (c : Cocone F) : Cocone (rightFibrationCommonDiagram F) :=
  (edgewiseOrdinaryLift (RightFibrationObject B)).mapCocone c

/-- 共通余錐の右射影は元の同じ余錐の全 join 射。 -/
lemma rightFibrationCommonCocone_coherentRight (c : Cocone F) :
    (strictNativeCocone (rightFibrationCommonCocone c)).val ≫
      (edgewiseEnrichedInfinityEquivalence (RightFibrationObject B)).hom =
        (strictNativeCocone c).val := by
  change _ ≫ coherentNerveMap (edgewiseEnrichedRight (RightFibrationObject B)) = _
  rw [strictNativeCocone_postcomp_val]
  change (strictNativeCocone ((edgewiseOrdinaryLift (RightFibrationObject B) ⋙
    coherentEnrichedUnderlyingFunctor
      (edgewiseEnrichedRight (RightFibrationObject B))).mapCocone c)).val = _
  rw [edgewiseOrdinaryLift_right]
  rfl

/-- 共通余錐の反転脚は同じ通常の反転余錐の全 join 射。 -/
lemma rightFibrationCommonCocone_coherentOpposite (c : Cocone F) :
    (strictNativeCocone (rightFibrationCommonCocone c)).val ≫
      coherentNerveMap (rightFibrationOppositeEnriched B) =
        (strictNativeCocone ((rightFibrationOppositeOrdinary B).mapCocone c)).val := by
  rw [strictNativeCocone_postcomp_val]
  change (strictNativeCocone ((edgewiseOrdinaryLift (RightFibrationObject B) ⋙
    coherentEnrichedUnderlyingFunctor (rightFibrationOppositeEnriched B)).mapCocone c)).val = _
  rw [edgewiseOrdinaryLift_rightFibrationOpposite]

/-- 元の同じ余錐への実際の反転は、通常の反転余錐と全高次パラメーターで関手同型。 -/
def strictRightFibrationOppositeCoconeIso (c : Cocone F) :
    FunctorIso ((strictNativeCocone c).val ≫ rightFibrationOppositeInfinityMap B)
      (strictNativeCocone ((rightFibrationOppositeOrdinary B).mapCocone c)).val := by
  let E := edgewiseEnrichedInfinityEquivalence (RightFibrationObject B)
  let R := (strictNativeCocone (rightFibrationCommonCocone c)).val
  let O := coherentNerveMap (rightFibrationOppositeEnriched B)
  have he := (E.homInvIso.precomp R).postcomp O
  change FunctorIso ((R ≫ E.hom) ≫ (E.inv ≫ O)) (R ≫ O) at he
  have hr : R ≫ E.hom = (strictNativeCocone c).val :=
    rightFibrationCommonCocone_coherentRight c
  have ho : R ≫ O =
      (strictNativeCocone ((rightFibrationOppositeOrdinary B).mapCocone c)).val :=
    rightFibrationCommonCocone_coherentOpposite c
  rw [hr, ho] at he
  exact he

end SerrePositivity.InfinityCategories.F2.Ind
