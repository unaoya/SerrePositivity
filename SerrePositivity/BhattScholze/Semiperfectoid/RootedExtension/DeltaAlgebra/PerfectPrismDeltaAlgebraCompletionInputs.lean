module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaAlgebra.DeltaAlgebraPerfectionCompletionResidue
public import SerrePositivity.BhattScholze.Prism.Basic.PerfectOrientedPrism
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerComplete

/-! # 完全prism上の実δ完全化逐次対象の完備性と還元入力 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (E : DeltaStructure p B) (j : A →+* B) (d : A)

/-- 同じ実δ完全化の逐次対象は、d完備化後もp導来完備。 -/
theorem deltaAlgebraPerfectionIteratedPDCompletion_isComplete_p :
    IsComplete A (p : A) (DeltaAlgebraPerfectionIteratedPDCompletion E j d).obj := by
  let X := boundedAboveDerivedSingleFunctor.obj
    (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j))
  let Y := (boundedAboveDerivedCompletionFunctor A (p : A)).obj X
  have hY : IsComplete A (p : A) Y.obj :=
    derivedComplexCompletionFunctor_isComplete A (p : A) X.obj
  let K := DerivedCategory.Q.objPreimage Y.obj
  let eK : DerivedCategory.Q.obj K ≅ Y.obj := DerivedCategory.Q.objObjPreimageIso Y.obj
  have hK : IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
    isComplete_of_iso A (p : A) eK.symm hY
  have hstage (n : ℕ) : IsComplete A (p : A)
      (DerivedCategory.Q.obj (complexPowerKoszulStage A d K n)) :=
    isComplete_Q_mappingCone A (p : A) (smulId (d ^ n) K) hK hK
  have hC : IsComplete A (p : A) (complexCompletionObject A d K) :=
    isComplete_complexTowerHomotopyLimitObject_of_stages A (p : A)
      (complexPowerKoszulStage A d K) (complexPowerKoszulTransition A d K) hstage
  let e : complexCompletionObject A d K ≅
      (DeltaAlgebraPerfectionIteratedPDCompletion E j d).obj :=
    (derivedComplexCompletionComparison A d).symm.app K ≪≫
      (derivedComplexCompletionFunctor A d).mapIso eK
  exact isComplete_of_iso A (p : A) e hC

/-- 同じ具体的逐次対象は、最後の主元完備化によりd導来完備。 -/
theorem deltaAlgebraPerfectionIteratedPDCompletion_isComplete_d :
    IsComplete A d (DeltaAlgebraPerfectionIteratedPDCompletion E j d).obj :=
  derivedComplexCompletionFunctor_isComplete A d
    ((boundedAboveDerivedCompletionFunctor A (p : A)).obj
      (boundedAboveDerivedSingleFunctor.obj
        (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j)))).obj

/-- 完全prism上の実逐次対象の完備性と還元入力。元Bの還元条件は明示する。 -/
theorem perfectPrismDeltaAlgebraCompletion_residue_inputs
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (hj : P.deltaStructure.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) i).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
    (hFF : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), P.generator})
      ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) 0).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj)) :
    let X := DeltaAlgebraPerfectionIteratedPDCompletion E j P.generator
    let Y := (boundedAboveDerivedBaseChange
      (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj X
    IsComplete A (p : A) X.obj ∧ IsComplete A P.generator X.obj ∧
      (∀ i : ℤ, i ≠ 0 → IsZero
        ((DerivedCategory.homologyFunctor
          (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) i).obj Y.obj)) ∧
      Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), P.generator})
        ((DerivedCategory.homologyFunctor
          (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) 0).obj Y.obj) := by
  refine ⟨deltaAlgebraPerfectionIteratedPDCompletion_isComplete_p E j P.generator,
    deltaAlgebraPerfectionIteratedPDCompletion_isComplete_d E j P.generator, ?_, ?_⟩
  · exact deltaAlgebraPerfectionCompletionResidue_homology_isZero
      P.deltaStructure E j P.generator hP hj P.generator_regular hzero hFF
  · exact deltaAlgebraPerfectionCompletionResidueH0_faithfullyFlat
      P.deltaStructure E j P.generator hP hj P.generator_regular hzero hFF

end SerrePositivity.BhattScholze
