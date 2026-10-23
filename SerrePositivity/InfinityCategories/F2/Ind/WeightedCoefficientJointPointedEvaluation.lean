module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientJointEvaluation
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientEvaluation
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.PointedIdentity

/-!
概要：元の全評価の係数制限の pointed 成分は、同じ係数評価の pointed 成分そのもの。
方針：元の共同分類への厳密な因子分解に、同じ小さい unstraightening の pointed 自然性を使う。
規約：元の全評価と同じ係数復元を固定。使われ方：指定 native 評価値写像の因子分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I)
local notation "G" => weightedDensityJointTargetDiagram F
local notation "Q" => weightedLeftCoefficientDiagram (F ⋙ rightFibrationOppositeOrdinary C) i
local notation "J" => leftStraighteningInfinityDiagram
  (leftFibrationWeightedProjection (F ⋙ rightFibrationOppositeOrdinary C))

local instance weightedCoefficientPointedJointBase_quasicategory : Quasicategory (C.op ⊗ nerve I) :=
  quasicategory_of_innerFibration (fst C.op (nerve I))

/-- 元の全評価の同じ係数での pointed 成分は、同じ係数評価・復元の pointed 成分。 -/
lemma weightedCoefficientJointEvaluation_pointed :
    (SSet.uliftFunctor.{u + 1, u}).map (weightedTwistedCoefficientIntoTotal F i) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (weightedDensityTwistedJointMap F) ≫
        smallLeftUnstraighteningPointedMap G =
    (SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientEvaluation F i) ≫
      smallLeftUnstraighteningPointedMap Q := by
  have h := congrArg (fun f ↦ (SSet.uliftFunctor.{u + 1, u}).map f ≫
    smallLeftUnstraighteningPointedMap J) (weightedCoefficientJointEvaluation_factorization F i)
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc,
    smallLeftUnstraighteningPointedMap_naturality, weightedCoefficientEvaluation] using h

end SerrePositivity.InfinityCategories.F2.Ind
