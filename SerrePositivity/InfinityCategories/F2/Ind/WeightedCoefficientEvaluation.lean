module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedCoefficientCanonicalIso
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedLeftCoefficientEquivalence
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorPostLaws

/-!
概要：指定係数評価と同じ共同復元の合成を、元の twisted-arrow 評価の像へ相対比較する。
方針：構成済みの係数持ち上げの同型を、同じ底を保つ係数復元で後合成する。
規約：元の係数図式と復元射を固定。使われ方：指定 native 密度余錐の評価判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C) (i : I)
local notation "Q" => weightedLeftCoefficientDiagram (F ⋙ rightFibrationOppositeOrdinary C) i
local notation "R" => weightedLeftCoefficientRecovery (F ⋙ rightFibrationOppositeOrdinary C) i

/-- 元の全評価の係数制限と同じ係数復元の合成。 -/
def weightedCoefficientEvaluation : pullback (edgewiseRight C) (F.obj i).val.hom ⟶
    smallLeftUnstraightening Q := weightedTwistedCoefficientLift F i ≫ R

/-- 同じ係数評価は元の twisted arrow の始点への射影を保つ。 -/
lemma weightedCoefficientEvaluation_projection :
    weightedCoefficientEvaluation F i ≫ smallLeftUnstraighteningProjection Q =
      pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C := by
  rw [weightedCoefficientEvaluation, Category.assoc, weightedLeftCoefficientRecovery_projection]
  exact weightedTwistedCoefficientLift_projection F i

/-- 同じ評価は、元の twisted-arrow 持ち上げを同じ係数復元で写したものと底上で同型。 -/
def weightedCoefficientEvaluation_canonicalIso : VertexIso
    (relativeFunctorVertex (smallLeftUnstraighteningProjection Q)
      (pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C)
      (weightedCoefficientEvaluation F i) (weightedCoefficientEvaluation_projection F i))
    (relativeFunctorVertex (smallLeftUnstraighteningProjection Q)
      (pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C)
      (twistedArrowSourceLift (F.obj i).val.hom ≫ R)
      (by rw [Category.assoc, weightedLeftCoefficientRecovery_projection]
          exact twistedArrowSourceLift_projection (F.obj i).val.hom)) := by
  let a := pullback.fst (edgewiseRight C) (F.obj i).val.hom ≫ edgewiseLeft C
  have hR := weightedLeftCoefficientRecovery_projection
    (F ⋙ rightFibrationOppositeOrdinary C) i
  have h₁ := relativeFunctorPost_vertex (SSet.opFunctor.map (F.obj i).val.hom)
    (smallLeftUnstraighteningProjection Q) R hR a
    (weightedTwistedCoefficientLift F i) (weightedTwistedCoefficientLift_projection F i)
  have h₂ := relativeFunctorPost_vertex (SSet.opFunctor.map (F.obj i).val.hom)
    (smallLeftUnstraighteningProjection Q) R hR a
    (twistedArrowSourceLift (F.obj i).val.hom)
    (twistedArrowSourceLift_projection (F.obj i).val.hom)
  exact eqToIso (congrArg SSet.HomotopyCategory.mk h₁.symm) ≪≫
    (weightedTwistedCoefficientLift_canonicalIso F i).map
      (HomotopyLimits.relativeFunctorPost _ _ R hR a) ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk h₂)

end SerrePositivity.InfinityCategories.F2.Ind
