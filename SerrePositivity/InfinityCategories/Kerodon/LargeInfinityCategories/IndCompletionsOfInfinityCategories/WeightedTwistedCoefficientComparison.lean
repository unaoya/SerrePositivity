module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedTwistedCoefficientLift
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RelativeEvaluationIsoTransport

/-!
概要：元の全評価から戻した係数評価は、元の全 twisted-arrow 左端評価と相対同型。
方針：同じ係数グラフの厳密な相対関手空間同型で、全族の指定比較を回収する。
規約：元の反転全空間と底を固定。使われ方：指定された fiber 密度余錐の普遍性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C) (i : I)

/-- 元の係数の全 twisted arrow の始点を、元の反対底で読む射。 -/
abbrev weightedTwistedCoefficientBase : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (F.obj i).val.left ⟶ C.op :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (F.obj i).val.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft C

/-- 元の全比較を係数へ制限した底は、元の係数の同じ始点と同じ添字グラフ。 -/
lemma weightedTwistedCoefficient_base :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightTwistedTotalDiagram F) i ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedRightTwistedComparison F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedSourceBase F) =
        weightedTwistedCoefficientBase F i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase C.op i := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedRightTwistedComparison_coefficient F i, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedSourceBase_coefficient F i, ← Category.assoc, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeEdgewiseRightComparison_fst]

/-- 元の全評価を係数へ制限すると、同じ元の係数評価の全空間への像になる。 -/
lemma weightedTwistedCoefficient_evaluation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightTwistedTotalDiagram F) i ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedRightTwistedComparison F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedSourceLift F).map) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeEdgewiseRightComparison (F.obj i).val.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedCoefficientLift F i) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationTotalDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C)) i := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedRightTwistedComparison_coefficient F i, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedCoefficientLift_inclusion F i, ← Category.assoc]

/-- 同じ係数評価は、元の全 twisted-arrow 左端射影と同じ底上で相対同型。 -/
def weightedTwistedCoefficientLift_evaluationIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (SSet.opFunctor.map (F.obj i).val.hom)
      (weightedTwistedCoefficientBase F i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeEdgewiseRightComparison (F.obj i).val.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedCoefficientLift F i)
      (by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedCoefficientLift_projection, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeEdgewiseRightComparison_fst]))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex (SSet.opFunctor.map (F.obj i).val.hom)
      (weightedTwistedCoefficientBase F i) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (F.obj i).val.left)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_naturality (F.obj i).val.hom).symm) := by
  have : Quasicategory (C.op ⊗ nerve I) :=
    quasicategory_of_innerFibration (fst C.op (nerve I))
  have : Quasicategory (F.obj i).val.left :=
    quasicategory_of_innerFibration (F.obj i).val.hom
  have : Quasicategory
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationTotalDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C))) :=
    quasicategory_of_innerFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationWeightedProjection (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C))
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficient_isPullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationDiagramProjection (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C)) i)
    (weightedTwistedCoefficientBase F i)
    (weightedTwistedCoefficientBase F i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase C.op i) rfl)
  apply e.isQCatEquivalence.isFullyFaithful.preimageVertexIso
  dsimp only [e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso]
  have hL : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeEdgewiseRightComparison (F.obj i).val.hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedCoefficientLift F i) ≫ SSet.opFunctor.map (F.obj i).val.hom =
        weightedTwistedCoefficientBase F i := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedCoefficientLift_projection, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.relativeEdgewiseRightComparison_fst]
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (F.obj i).val.left ≫ SSet.opFunctor.map (F.obj i).val.hom =
      weightedTwistedCoefficientBase F i := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_naturality (F.obj i).val.hom).symm
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackIso_vertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficient_isPullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationDiagramProjection (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C)) i)
    (weightedTwistedCoefficientBase F i)
    (weightedTwistedCoefficientBase F i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase C.op i) rfl _ hL
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackIso_vertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedCoefficient_isPullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationDiagramProjection (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary C)) i)
    (weightedTwistedCoefficientBase F i)
    (weightedTwistedCoefficientBase F i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase C.op i) rfl _ hR
  refine eqToIso (congrArg SSet.HomotopyCategory.mk h₁) ≪≫ ?_ ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk h₂.symm)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeEvaluationIsoOfEq (weightedTwistedCoefficient_base F i)
    (weightedTwistedCoefficient_evaluation F i) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTwistedSourceLift_coefficientIso F i)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
