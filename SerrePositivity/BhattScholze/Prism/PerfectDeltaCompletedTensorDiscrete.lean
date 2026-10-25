module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PerfectResidueCompletedTensor
public import SerrePositivity.BhattScholze.Delta.PerfectDeltaModP
/-! # The actual p-completed tensor of perfect delta rings is discrete

The p-regularity and perfect residue inputs are supplied by the original delta
structures. This proves discreteness, p-regularity and classical completeness of
H0, and does not yet construct a perfect delta structure on that H0 ring.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
  [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- A perfect delta algebra has regular base-scalar p action. -/
lemma perfectDeltaAlgebra_p_regular (DS : DeltaStructure p S) (hS : DS.IsPerfect) :
    IsSMulRegular (ModuleCat.of R S) (p : R) := by
  intro x y hxy
  apply hS.p_mul_injective
  change (p : R) • (show S from x) = (p : R) • (show S from y) at hxy
  simpa only [Algebra.smul_def, map_natCast] using hxy

/-- Its actual residue over the base ideal is a perfect ring. -/
lemma perfectDeltaAlgebra_perfectRing_residue (DS : DeltaStructure p S) (hS : DS.IsPerfect) :
    PerfectRing (S ⧸ Ideal.map (algebraMap R S) (Ideal.span {(p : R)})) p := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  exact hS.perfectRing_mod_p

/-- The original completed tensor of perfect delta rings is discrete. -/
lemma perfectDelta_completedTensor_pure
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect) :
    let X := (boundedAboveCompletedTensorAlgebra R (p : R) S T).X
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧ Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj => (p : R) • x) := by
  have := hR.perfectRing_mod_p
  have := perfectDeltaAlgebra_perfectRing_residue p R S DS hS
  have := perfectDeltaAlgebra_perfectRing_residue p R T DT hT
  exact completedTensorAlgebra_pure_of_perfect_residue p R S T hR.p_mul_injective
    (perfectDeltaAlgebra_p_regular p R S DS hS) (perfectDeltaAlgebra_p_regular p R T DT hT)

/-- Multiplication by p on its original H0 ring is injective. -/
lemma perfectDelta_completedTensorH0_p_mul_injective
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect) :
    let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
    letI := derivedH0CommRing A
    Function.Injective (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj =>
      (p : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) * x) := by
  have := hR.perfectRing_mod_p
  have := perfectDeltaAlgebra_perfectRing_residue p R S DS hS
  have := perfectDeltaAlgebra_perfectRing_residue p R T DT hT
  exact completedTensorH0_p_mul_injective_of_perfect_residue p R S T hR.p_mul_injective
    (perfectDeltaAlgebra_p_regular p R S DS hS) (perfectDeltaAlgebra_p_regular p R T DT hT)

/-- Its original H0 ring is classically p-adically complete. -/
lemma perfectDelta_completedTensorH0_isAdicComplete
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect) :
    let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
    letI := derivedH0CommRing A
    IsAdicComplete
      (Ideal.span {(p : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj)})
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) := by
  have := hR.perfectRing_mod_p
  have := perfectDeltaAlgebra_perfectRing_residue p R S DS hS
  have := perfectDeltaAlgebra_perfectRing_residue p R T DT hT
  exact completedTensorH0_isAdicComplete_of_perfect_residue p R S T hR.p_mul_injective
    (perfectDeltaAlgebra_p_regular p R S DS hS) (perfectDeltaAlgebra_p_regular p R T DT hT)
end SerrePositivity.BhattScholze
