module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedCoefficientComparison
public import SerrePositivity.InfinityCategories.F2.Ind.TwistedArrowSourceLiftRestrictionIso

/-!
概要：同じ全評価の係数は、元の right fibration の同じ全 twisted-arrow 持ち上げと相対同型。
方針：元の相対右端比較の前合成同値で、元の左端評価との二つの指定同型を回収する。
規約：元の係数全空間と射影を固定。使われ方：指定 fiber 密度余錐への元の評価の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I)

/-- 元の全評価の係数は、同じ元の全 twisted-arrow 持ち上げと同じ反対底上で相対同型。 -/
def weightedTwistedCoefficientLift_canonicalIso : VertexIso
    (relativeFunctorVertex (SSet.opFunctor.map (F.obj i).val.hom)
      (pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C)
      (weightedTwistedCoefficientLift F i) (weightedTwistedCoefficientLift_projection F i))
    (relativeFunctorVertex (SSet.opFunctor.map (F.obj i).val.hom)
      (pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C)
      (twistedArrowSourceLift (F.obj i).val.hom)
      (twistedArrowSourceLift_projection (F.obj i).val.hom)) := by
  have : Quasicategory (F.obj i).val.left :=
    quasicategory_of_innerFibration (F.obj i).val.hom
  have : Quasicategory (edgewiseSubdivision (F.obj i).val.left) :=
    twistedArrow_quasicategory (F.obj i).val.left
  have : RightFibration (pullback.fst (edgewiseRight C) (F.obj i).val.hom) :=
    ⟨rightFibrations.pullback_fst _ _ (RightFibration.mem (p := (F.obj i).val.hom))⟩
  have : Quasicategory (pullback (edgewiseRight C) (F.obj i).val.hom) :=
    quasicategory_of_innerFibration (pullback.fst (edgewiseRight C) (F.obj i).val.hom)
  have hr := (isQCatEquivalence_of_trivialKanFibration
    (relativeEdgewiseRightComparison (F.obj i).val.hom)).isPrecompositionEquivalence
  have hp := relativeFunctorPre_isQCatEquivalence_of_precompositionEquivalence
    (SSet.opFunctor.map (F.obj i).val.hom)
    (pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C)
    (relativeEdgewiseRightComparison (F.obj i).val.hom) hr
  apply hp.isFullyFaithful.preimageVertexIso
  have h₁ := relativeFunctorPre_vertex (SSet.opFunctor.map (F.obj i).val.hom)
    (pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C)
    (relativeEdgewiseRightComparison (F.obj i).val.hom) (weightedTwistedCoefficientLift F i)
    (weightedTwistedCoefficientLift_projection F i)
  have h₂ := relativeFunctorPre_vertex (SSet.opFunctor.map (F.obj i).val.hom)
    (pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C)
    (relativeEdgewiseRightComparison (F.obj i).val.hom)
    (twistedArrowSourceLift (F.obj i).val.hom)
    (twistedArrowSourceLift_projection (F.obj i).val.hom)
  refine eqToIso (congrArg SSet.HomotopyCategory.mk h₁) ≪≫ ?_ ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk h₂.symm)
  exact relativeEvaluationIsoOfEq
    (show weightedTwistedCoefficientBase F i =
      relativeEdgewiseRightComparison (F.obj i).val.hom ≫
        (pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C) by
          rw [← Category.assoc, relativeEdgewiseRightComparison_fst])
    rfl rfl ((weightedTwistedCoefficientLift_evaluationIso F i) ≪≫
      (twistedArrowSourceLift_restrictIso (F.obj i).val.hom).symm)

end SerrePositivity.InfinityCategories.F2.Ind
