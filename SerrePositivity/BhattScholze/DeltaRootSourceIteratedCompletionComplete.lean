module

public import SerrePositivity.BhattScholze.DeltaRootSourceIteratedCompletionResidue
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerComplete

/-! # 具体的根添加逐次対象のp方向・d方向の導来完備性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)

/-- 実p完備化後に実d完備化を施した具体的根添加対象は、なおp導来完備。 -/
theorem deltaRootSourceIteratedPDCompletion_isComplete_p :
    DerivedCompletion.IsComplete A (p : A)
      (DeltaRootSourceIteratedPDCompletion D d b).obj := by
  let X := DeltaRootSourceCoefficientObject d D b
  let Y := (DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj X
  have hY : DerivedCompletion.IsComplete A (p : A) Y.obj :=
    DerivedCompletion.derivedComplexCompletionFunctor_isComplete A (p : A) X.obj
  let K := DerivedCategory.Q.objPreimage Y.obj
  let eK : DerivedCategory.Q.obj K ≅ Y.obj := DerivedCategory.Q.objObjPreimageIso Y.obj
  have hK : DerivedCompletion.IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
    DerivedCompletion.isComplete_of_iso A (p : A) eK.symm hY
  have hstage (n : ℕ) : DerivedCompletion.IsComplete A (p : A)
      (DerivedCategory.Q.obj (DerivedCompletion.complexPowerKoszulStage A d K n)) :=
    DerivedCompletion.isComplete_Q_mappingCone A (p : A)
      (smulId (d ^ n) K) hK hK
  have hC : DerivedCompletion.IsComplete A (p : A)
      (DerivedCompletion.complexCompletionObject A d K) :=
    DerivedCompletion.isComplete_complexTowerHomotopyLimitObject_of_stages A (p : A)
      (DerivedCompletion.complexPowerKoszulStage A d K)
      (DerivedCompletion.complexPowerKoszulTransition A d K) hstage
  let e : DerivedCompletion.complexCompletionObject A d K ≅
      (DeltaRootSourceIteratedPDCompletion D d b).obj :=
    (DerivedCompletion.derivedComplexCompletionComparison A d).symm.app K ≪≫
      (DerivedCompletion.derivedComplexCompletionFunctor A d).mapIso eK
  exact DerivedCompletion.isComplete_of_iso A (p : A) e hC

/-- 同じ具体的逐次対象は、最後の主元完備化によりd導来完備。 -/
theorem deltaRootSourceIteratedPDCompletion_isComplete_d :
    DerivedCompletion.IsComplete A d
      (DeltaRootSourceIteratedPDCompletion D d b).obj :=
  DerivedCompletion.derivedComplexCompletionFunctor_isComplete A d
    ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
      (DeltaRootSourceCoefficientObject d D b)).obj

end SerrePositivity.BhattScholze
