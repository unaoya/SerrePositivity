module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientSourceComparison
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedDensityDiagramHomotopy
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation

/-!
概要：元の共同密度変換の底を係数・始点へ制限し、元の評価図式と定値標的を回収する。
方針：共同 Hom の curry 評価式と、同じ係数グラフの共同分類を使う。
規約：同じ全図式の制限。使われ方：c1 の底変換自然性を指定係数余錐へ入力する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I) (x : C _⦋0⦌)
local notation "W" => weightedNerve (rightFibrationTotalDiagram F)
local notation "Q" => weightedLeftCoefficientDiagram (F ⋙ rightFibrationOppositeOrdinary C) i

/-- 元の係数全空間上の Yoneda 図式を、元の指定始点で評価する。 -/
def weightedCoefficientEvaluationDiagram :=
  (SSet.uliftFunctor.{u + 1, u}).map (F.obj i).val.hom ≫
    yonedaInfinityMap C ≫ presheafInfinityEvaluation x

/-- 同じ係数分類の、同じ指定始点での値。 -/
def weightedCoefficientEvaluationVertex :=
  (weightedLeftCoefficientDiagram (F ⋙ rightFibrationOppositeOrdinary C) i).app
    (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm x))

/-- 元の共同密度図式へ、同じ係数と指定始点を含める。 -/
def weightedCoefficientEvaluationBase : (F.obj i).val.left ⟶ C.op ⊗ W :=
  lift (SSet.const (SSet.opObjEquiv.symm x))
    (weightedNerveConstantLift (rightFibrationTotalDiagram F) i)

/-- 元の共同 Hom の同じ制限は、元の係数 Yoneda 図式の同じ評価。 -/
lemma weightedCoefficientEvaluationBase_source :
    (SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientEvaluationBase F i x) ≫
      twistedElementsHomDiagram (weightedDensityProjection F) =
        weightedCoefficientEvaluationDiagram F i x := by
  have h : (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (rightFibrationTotalDiagram F) i) ≫
      (curry ((HomotopyLimits.uliftTensorIso.{u, u + 1} C.op W).inv ≫
        twistedElementsHomDiagram (weightedDensityProjection F)) ≫
          evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x))) =
      weightedCoefficientEvaluationDiagram F i x := by
    rw [weightedDensity_source_curry, ← Category.assoc, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, weightedDensityProjection_coefficient]
    rfl
  rw [← h, curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 元の共同分類の同じ制限は、同じ係数分類の指定値に定値。 -/
lemma weightedCoefficientEvaluationBase_target :
    (SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientEvaluationBase F i x) ≫
      weightedDensityJointTargetDiagram F = SSet.const (weightedCoefficientEvaluationVertex F i x) := by
  have hk : weightedCoefficientEvaluationBase F i x ≫ weightedTwistedNativeJointBase F =
      (SSet.const (SSet.opObjEquiv.symm x) : (F.obj i).val.left ⟶ C.op) ≫
        underSectionFiberBase C.op i := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, weightedCoefficientEvaluationBase,
        weightedTwistedNativeJointBase, underSectionFiberBase, lift_fst, Category.comp_id]
    · simp only [Category.assoc, weightedCoefficientEvaluationBase,
        weightedTwistedNativeJointBase, underSectionFiberBase, lift_snd, lift_snd_assoc,
        SSet.comp_const]
      exact weightedNerveConstantLift_projection (rightFibrationTotalDiagram F) i
  rw [weightedDensityJointTargetDiagram, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, hk, CategoryTheory.Functor.map_comp, Category.assoc]
  change (SSet.uliftFunctor.{u + 1, u}).map (SSet.const (SSet.opObjEquiv.symm x)) ≫ Q = _
  have hu : (SSet.uliftFunctor.{u + 1, u}).map
      (SSet.const (SSet.opObjEquiv.symm x) : (F.obj i).val.left ⟶ C.op) =
      SSet.const (ULift.up (SSet.opObjEquiv.symm x)) := rfl
  rw [hu, SSet.const_comp]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
