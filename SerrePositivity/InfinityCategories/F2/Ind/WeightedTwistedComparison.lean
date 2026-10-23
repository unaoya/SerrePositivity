module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedMapTrivialKan
public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightTwistedEvaluation
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.LeftFibration
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveInnerFibration

/-!
概要：元の自然な twisted-arrow 相対比較は、weighted 全空間でも前合成同値。
方針：全成分の自明 Kan 性から同じ全写像の自明 Kan 性を得て、同値を結論する。
規約：追加の同値性・モデル圏仮定なし。使われ方：元の全密度変換の coherent な降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)

/-- 元の全図式に自然な比較を、そのまま元の weighted 全空間へ写す。 -/
def weightedRightTwistedComparison : weightedNerve (strictRightTwistedTotalDiagram F) ⟶
    weightedNerve (strictRightTwistedElementsDiagram F) :=
  weightedNerveMap (strictRightTwistedComparison F)

instance weightedRightTwistedComparison_trivialKanFibration :
    TrivialKanFibration (weightedRightTwistedComparison F) :=
  weightedMap_trivialKanFibration (strictRightTwistedComparison F)

/-- 同じ全比較は元の添字への射影を厳密に保つ。 -/
lemma weightedRightTwistedComparison_projection :
    weightedRightTwistedComparison F ≫
      weightedNerveProjection (strictRightTwistedElementsDiagram F) =
        weightedNerveProjection (strictRightTwistedTotalDiagram F) :=
  weightedNerveMap_projection (strictRightTwistedComparison F)

/-- 元の全比較自身が前合成同値であり、係数の全空間の Kan 性を要求しない。 -/
lemma weightedRightTwistedComparison_isPrecompositionEquivalence [Quasicategory C] :
    IsPrecompositionEquivalence (weightedRightTwistedComparison F) := by
  have (i : I) : Quasicategory (F.obj i).val.left :=
    quasicategory_of_innerFibration (F.obj i).val.hom
  have (i : I) : Quasicategory ((strictRightTwistedTotalDiagram F).obj i) := by
    change Quasicategory (TwistedArrow (F.obj i).val.left)
    infer_instance
  have (i : I) : RightFibration (pullback.fst (edgewiseRight C) (F.obj i).val.hom) :=
    ⟨rightFibrations.pullback_fst _ _ (RightFibration.mem (p := (F.obj i).val.hom))⟩
  have (i : I) : Quasicategory ((strictRightTwistedElementsDiagram F).obj i) :=
    quasicategory_of_innerFibration (pullback.fst (edgewiseRight C) (F.obj i).val.hom)
  exact (isQCatEquivalence_of_trivialKanFibration
    (weightedRightTwistedComparison F)).isPrecompositionEquivalence

end SerrePositivity.InfinityCategories.F2.Ind
