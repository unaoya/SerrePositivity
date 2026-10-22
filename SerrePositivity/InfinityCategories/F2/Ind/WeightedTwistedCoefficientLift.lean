module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientGraph

/-!
概要：元の全評価の各係数を、元の right fibration の反転全空間へ戻す。
方針：同じ添字のグラフの引き戻し性で、同じ全評価の係数制限を一意に持ち上げる。
規約：元の全空間への射と底への射を保持。使われ方：指定された fiber 密度評価の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I)

/-- 元の twisted-arrow 係数包含は、元の始点射影と同じ添字グラフを保つ。 -/
lemma weightedTwistedSourceBase_coefficient :
    weightedNerveConstantLift (strictRightTwistedElementsDiagram F) i ≫
      weightedTwistedSourceBase F =
        (pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C) ≫
          underSectionFiberBase C.op i :=
  weightedCoefficient_graph_commute (strictRightTwistedSourceProjection F) i

/-- 同じ全評価の係数制限を、元の反転した全空間の値へ戻す。 -/
def weightedTwistedCoefficientLift : pullback (edgewiseRight C) (F.obj i).val.hom ⟶
    (F.obj i).val.left.op :=
  (weightedCoefficient_isPullback
    (leftFibrationDiagramProjection (F ⋙ rightFibrationOppositeOrdinary C)) i).lift
      (weightedNerveConstantLift (strictRightTwistedElementsDiagram F) i ≫
        (weightedTwistedSourceLift F).map)
      (pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C) (by
        change (weightedNerveConstantLift (strictRightTwistedElementsDiagram F) i ≫
            (weightedTwistedSourceLift F).map) ≫
          leftFibrationWeightedProjection (F ⋙ rightFibrationOppositeOrdinary C) = _
        rw [Category.assoc, (weightedTwistedSourceLift F).over_base,
          weightedTwistedSourceBase_coefficient])

/-- 同じ係数の評価を元の全空間へ戻すと、元の全評価の制限そのもの。 -/
lemma weightedTwistedCoefficientLift_inclusion :
    weightedTwistedCoefficientLift F i ≫ weightedNerveConstantLift
      (leftFibrationTotalDiagram (F ⋙ rightFibrationOppositeOrdinary C)) i =
        weightedNerveConstantLift (strictRightTwistedElementsDiagram F) i ≫
          (weightedTwistedSourceLift F).map :=
  (weightedCoefficient_isPullback
    (leftFibrationDiagramProjection (F ⋙ rightFibrationOppositeOrdinary C)) i).lift_fst _ _ _

/-- 元の係数評価は、元の反対底の同じ twisted-arrow 始点を厳密に保つ。 -/
lemma weightedTwistedCoefficientLift_projection :
    weightedTwistedCoefficientLift F i ≫ SSet.opFunctor.map (F.obj i).val.hom =
      pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C :=
  (weightedCoefficient_isPullback
    (leftFibrationDiagramProjection (F ⋙ rightFibrationOppositeOrdinary C)) i).lift_snd _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
