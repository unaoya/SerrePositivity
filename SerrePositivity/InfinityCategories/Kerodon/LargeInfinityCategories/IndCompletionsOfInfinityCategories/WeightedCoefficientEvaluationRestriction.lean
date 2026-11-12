module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedCoefficientSourceComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedDensityDiagramHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：元の共同密度変換の底を係数・始点へ制限し、元の評価図式と定値標的を回収する。
方針：共同 Hom の curry 評価式と、同じ係数グラフの共同分類を使う。
規約：同じ全図式の制限。使われ方：c1 の底変換自然性を指定係数余錐へ入力する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C) (i : I) (x : C _⦋0⦌)
local notation "W" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F)
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedLeftCoefficientDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C) i

/-- 元の係数全空間上の Yoneda 図式を、元の指定始点で評価する。 -/
def weightedCoefficientEvaluationDiagram :=
  (SSet.uliftFunctor.{u + 1, u}).map (F.obj i).val.hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation x

/-- 同じ係数分類の、同じ指定始点での値。 -/
def weightedCoefficientEvaluationVertex :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedLeftCoefficientDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C) i).app
    (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm x))

/-- 元の共同密度図式へ、同じ係数と指定始点を含める。 -/
def weightedCoefficientEvaluationBase : (F.obj i).val.left ⟶ C.op ⊗ W :=
  lift (SSet.const (SSet.opObjEquiv.symm x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) i)

/-- 元の共同 Hom の同じ制限は、元の係数 Yoneda 図式の同じ評価。 -/
lemma weightedCoefficientEvaluationBase_source :
    (SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientEvaluationBase F i x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsHomDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityProjection F) =
        weightedCoefficientEvaluationDiagram F i x := by
  have h : (SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) i) ≫
      (curry ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} C.op W).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedElementsHomDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityProjection F)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x))) =
      weightedCoefficientEvaluationDiagram F i x := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensity_source_curry, ← Category.assoc, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityProjection_coefficient]
    rfl
  rw [← h, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- 元の共同分類の同じ制限は、同じ係数分類の指定値に定値。 -/
lemma weightedCoefficientEvaluationBase_target :
    (SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientEvaluationBase F i x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityJointTargetDiagram F = SSet.const (weightedCoefficientEvaluationVertex F i x) := by
  have hk : weightedCoefficientEvaluationBase F i x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedNativeJointBase F =
      (SSet.const (SSet.opObjEquiv.symm x) : (F.obj i).val.left ⟶ C.op) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase C.op i := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, weightedCoefficientEvaluationBase,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedNativeJointBase, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase, lift_fst, Category.comp_id]
    · simp only [Category.assoc, weightedCoefficientEvaluationBase,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedNativeJointBase, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase, lift_snd, lift_snd_assoc,
        SSet.comp_const]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedDensityJointTargetDiagram, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, hk, CategoryTheory.Functor.map_comp, Category.assoc]
  change (SSet.uliftFunctor.{u + 1, u}).map (SSet.const (SSet.opObjEquiv.symm x)) ≫ Q = _
  have hu : (SSet.uliftFunctor.{u + 1, u}).map
      (SSet.const (SSet.opObjEquiv.symm x) : (F.obj i).val.left ⟶ C.op) =
      SSet.const (ULift.up (SSet.opObjEquiv.symm x)) := rfl
  rw [hu, SSet.const_comp]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
