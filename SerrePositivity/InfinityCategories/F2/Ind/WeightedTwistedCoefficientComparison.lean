module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedCoefficientLift
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeEvaluationIsoTransport

/-!
概要：元の全評価から戻した係数評価は、元の全 twisted-arrow 左端評価と相対同型。
方針：同じ係数グラフの厳密な相対関手空間同型で、全族の指定比較を回収する。
規約：元の反転全空間と底を固定。使われ方：指定された fiber 密度余錐の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I)

/-- 元の係数の全 twisted arrow の始点を、元の反対底で読む射。 -/
abbrev weightedTwistedCoefficientBase : edgewiseSubdivision (F.obj i).val.left ⟶ C.op :=
  edgewiseSubdivisionMap (F.obj i).val.hom ≫ edgewiseLeft C

/-- 元の全比較を係数へ制限した底は、元の係数の同じ始点と同じ添字グラフ。 -/
lemma weightedTwistedCoefficient_base :
    weightedNerveConstantLift (strictRightTwistedTotalDiagram F) i ≫
      (weightedRightTwistedComparison F ≫ weightedTwistedSourceBase F) =
        weightedTwistedCoefficientBase F i ≫ underSectionFiberBase C.op i := by
  rw [← Category.assoc, weightedRightTwistedComparison_coefficient F i, Category.assoc,
    weightedTwistedSourceBase_coefficient F i, ← Category.assoc, ← Category.assoc,
    relativeEdgewiseRightComparison_fst]

/-- 元の全評価を係数へ制限すると、同じ元の係数評価の全空間への像になる。 -/
lemma weightedTwistedCoefficient_evaluation :
    weightedNerveConstantLift (strictRightTwistedTotalDiagram F) i ≫
      (weightedRightTwistedComparison F ≫ (weightedTwistedSourceLift F).map) =
        (relativeEdgewiseRightComparison (F.obj i).val.hom ≫ weightedTwistedCoefficientLift F i) ≫
          weightedNerveConstantLift
            (leftFibrationTotalDiagram (F ⋙ rightFibrationOppositeOrdinary C)) i := by
  rw [← Category.assoc, weightedRightTwistedComparison_coefficient F i, Category.assoc,
    ← weightedTwistedCoefficientLift_inclusion F i, ← Category.assoc]

/-- 同じ係数評価は、元の全 twisted-arrow 左端射影と同じ底上で相対同型。 -/
def weightedTwistedCoefficientLift_evaluationIso : VertexIso
    (relativeFunctorVertex (SSet.opFunctor.map (F.obj i).val.hom)
      (weightedTwistedCoefficientBase F i)
      (relativeEdgewiseRightComparison (F.obj i).val.hom ≫ weightedTwistedCoefficientLift F i)
      (by rw [Category.assoc, weightedTwistedCoefficientLift_projection, ← Category.assoc,
        relativeEdgewiseRightComparison_fst]))
    (relativeFunctorVertex (SSet.opFunctor.map (F.obj i).val.hom)
      (weightedTwistedCoefficientBase F i) (edgewiseLeft (F.obj i).val.left)
      (edgewiseLeft_naturality (F.obj i).val.hom).symm) := by
  have : Quasicategory (C.op ⊗ nerve I) :=
    quasicategory_of_innerFibration (fst C.op (nerve I))
  have : Quasicategory (F.obj i).val.left :=
    quasicategory_of_innerFibration (F.obj i).val.hom
  have : Quasicategory
      (weightedNerve (leftFibrationTotalDiagram (F ⋙ rightFibrationOppositeOrdinary C))) :=
    quasicategory_of_innerFibration
      (leftFibrationWeightedProjection (F ⋙ rightFibrationOppositeOrdinary C))
  let e := qCatEquivalenceOfIso (relativeFunctorIsPullbackIso
    (weightedCoefficient_isPullback
      (leftFibrationDiagramProjection (F ⋙ rightFibrationOppositeOrdinary C)) i)
    (weightedTwistedCoefficientBase F i)
    (weightedTwistedCoefficientBase F i ≫ underSectionFiberBase C.op i) rfl)
  apply e.isQCatEquivalence.isFullyFaithful.preimageVertexIso
  dsimp only [e, qCatEquivalenceOfIso]
  have hL : (relativeEdgewiseRightComparison (F.obj i).val.hom ≫
      weightedTwistedCoefficientLift F i) ≫ SSet.opFunctor.map (F.obj i).val.hom =
        weightedTwistedCoefficientBase F i := by
    rw [Category.assoc, weightedTwistedCoefficientLift_projection, ← Category.assoc,
      relativeEdgewiseRightComparison_fst]
  have hR : edgewiseLeft (F.obj i).val.left ≫ SSet.opFunctor.map (F.obj i).val.hom =
      weightedTwistedCoefficientBase F i := (edgewiseLeft_naturality (F.obj i).val.hom).symm
  have h₁ := relativeFunctorIsPullbackIso_vertex
    (weightedCoefficient_isPullback
      (leftFibrationDiagramProjection (F ⋙ rightFibrationOppositeOrdinary C)) i)
    (weightedTwistedCoefficientBase F i)
    (weightedTwistedCoefficientBase F i ≫ underSectionFiberBase C.op i) rfl _ hL
  have h₂ := relativeFunctorIsPullbackIso_vertex
    (weightedCoefficient_isPullback
      (leftFibrationDiagramProjection (F ⋙ rightFibrationOppositeOrdinary C)) i)
    (weightedTwistedCoefficientBase F i)
    (weightedTwistedCoefficientBase F i ≫ underSectionFiberBase C.op i) rfl _ hR
  refine eqToIso (congrArg SSet.HomotopyCategory.mk h₁) ≪≫ ?_ ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk h₂.symm)
  exact relativeEvaluationIsoOfEq (weightedTwistedCoefficient_base F i)
    (weightedTwistedCoefficient_evaluation F i) rfl (weightedTwistedSourceLift_coefficientIso F i)

end SerrePositivity.InfinityCategories.F2.Ind
