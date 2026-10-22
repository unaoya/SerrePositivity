module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientGraph
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningInfinityReconstruction
public import SerrePositivity.InfinityCategories.F1.LeftFibrationComparisonBaseChange

/-!
概要：共同 weighted 分類の元の復元射を各添字グラフへ戻し、元の係数全空間を復元する。
方針：同じグラフの同型、同じ復元射の底変換、小さい unstraightening の厳密な底変換を合成。
規約：元の係数射影を保持。使われ方：指定密度変換の各 fiber の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {B : SSet.{u}} [Quasicategory B] {I : Type u} [SmallCategory I]
  (F : I ⥤ LeftFibrationObject B) (i : I)
local notation "p" => leftFibrationWeightedProjection F
local notation "J" => leftStraighteningInfinityDiagram p
local notation "g" => underSectionFiberBase B i

local instance weightedCoefficientJointBase_quasicategory : Quasicategory (B ⊗ nerve I) :=
  quasicategory_of_innerFibration (fst B (nerve I))

/-- 同じ共同分類を、元の指定添字のグラフ上へ制限した同じ図式。 -/
def weightedLeftCoefficientDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map g ≫ J

/-- 元の係数全空間から、同じ共同分類の同じ係数の小さい復元への実際の射。 -/
def weightedLeftCoefficientRecovery : (F.obj i).val.left ⟶
    smallLeftUnstraightening (weightedLeftCoefficientDiagram F i) :=
  (weightedParameterGraphIso (leftFibrationDiagramProjection F) i).hom ≫
    fiberComparisonBaseChange p (smallLeftUnstraighteningProjection J)
      (leftStraighteningInfinityReconstruction p)
      (leftStraighteningInfinityReconstruction_projection p)
      g ≫ (smallLeftUnstraighteningBaseChangeIso J g).inv

/-- 同じ係数の復元は、元の係数の同じ底への射影を厳密に保つ。 -/
lemma weightedLeftCoefficientRecovery_projection :
    weightedLeftCoefficientRecovery F i ≫
      smallLeftUnstraighteningProjection (weightedLeftCoefficientDiagram F i) =
        (F.obj i).val.hom := by
  have h : (smallLeftUnstraighteningBaseChangeIso J g).inv ≫
      smallLeftUnstraighteningProjection (weightedLeftCoefficientDiagram F i) =
        pullback.snd (smallLeftUnstraighteningProjection J) g :=
    (smallLeftUnstraighteningMap_isPullback
      (weightedLeftCoefficientDiagram F i) J g rfl).isoPullback_inv_snd
  rw [weightedLeftCoefficientRecovery, Category.assoc, Category.assoc, h,
    fiberComparisonBaseChange_projection]
  exact weightedParameterGraphIso_snd (leftFibrationDiagramProjection F) i

/-- 元の共同復元への同じ係数の像は、元の係数包含による同じ復元の制限。 -/
lemma weightedLeftCoefficientRecovery_joint :
    weightedLeftCoefficientRecovery F i ≫
      smallLeftUnstraighteningMap (weightedLeftCoefficientDiagram F i) J g rfl =
        weightedNerveConstantLift (leftFibrationTotalDiagram F) i ≫
          leftStraighteningInfinityReconstruction p := by
  have h : (smallLeftUnstraighteningBaseChangeIso J g).inv ≫
      smallLeftUnstraighteningMap (weightedLeftCoefficientDiagram F i) J g rfl =
        pullback.fst (smallLeftUnstraighteningProjection J) g :=
    (smallLeftUnstraighteningMap_isPullback
      (weightedLeftCoefficientDiagram F i) J g rfl).isoPullback_inv_fst
  rw [weightedLeftCoefficientRecovery, Category.assoc, Category.assoc, h]
  simp only [fiberComparisonBaseChange, Category.assoc, pullback.lift_fst]
  rw [← Category.assoc]
  exact congrArg (fun f ↦ f ≫ leftStraighteningInfinityReconstruction p)
    (weightedParameterGraphIso_fst (leftFibrationDiagramProjection F) i)

end SerrePositivity.InfinityCategories.F2.Ind
