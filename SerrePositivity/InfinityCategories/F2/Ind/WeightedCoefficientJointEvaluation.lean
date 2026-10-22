module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedCoefficientIntoTotal
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientDiagramVertex
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedCoefficientLift

/-!
概要：元の全密度評価の係数制限は、同じ係数評価と同じ係数復元を通って共同分類へ写る。
方針：全評価の厳密な引き戻し公式と、同じ係数グラフの持ち上げの両射影を合成する。
規約：指定した全評価そのものの因子分解。使われ方：native 係数余錐の評価の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I)
local notation "p" => leftFibrationWeightedProjection (F ⋙ rightFibrationOppositeOrdinary C)
local notation "J" => leftStraighteningInfinityDiagram p

local instance weightedRightCoefficientJointBase_quasicategory : Quasicategory (C.op ⊗ nerve I) :=
  quasicategory_of_innerFibration (fst C.op (nerve I))

/-- 元の全評価の元の係数への制限は、同じ反転全空間を経た同じ係数復元の像。 -/
lemma weightedCoefficientJointEvaluation_factorization :
    weightedTwistedCoefficientIntoTotal F i ≫ weightedDensityTwistedJointMap F ≫
      smallLeftUnstraighteningMap (weightedDensityJointTargetDiagram F) J
        (weightedTwistedNativeJointBase F) rfl =
      weightedTwistedCoefficientLift F i ≫
        weightedLeftCoefficientRecovery (F ⋙ rightFibrationOppositeOrdinary C) i ≫
          smallLeftUnstraighteningMap
            (weightedLeftCoefficientDiagram (F ⋙ rightFibrationOppositeOrdinary C) i) J
            (underSectionFiberBase C.op i) rfl := by
  rw [weightedTwistedCoefficientIntoTotal, Category.assoc, weightedDensityTwistedJointMap_joint]
  simp only [weightedTwistedNativeLift, Category.assoc, Iso.hom_inv_id_assoc]
  rw [weightedLeftCoefficientRecovery_joint (F ⋙ rightFibrationOppositeOrdinary C) i]
  rw [← Category.assoc, ← weightedTwistedCoefficientLift_inclusion F i, Category.assoc]

end SerrePositivity.InfinityCategories.F2.Ind
