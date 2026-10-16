import SerrePositivity.BhattScholze.PerfectDeltaTensorStructure
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorFrobeniusEquiv
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorFrobeniusEquiv_tmul
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorFrobeniusEquiv_mod_p
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorStructure
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorStructure_frobeniusLift
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorStructure_isPerfect
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorStructure_includeLeft_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorStructure_includeRight_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorFrobeniusEquiv_symm_tmul
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorStructure_algebraMap_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorStructure_lift_isDeltaHom

#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorFrobeniusEquiv
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorFrobeniusEquiv_tmul
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorFrobeniusEquiv_mod_p
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorStructure
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorStructure_frobeniusLift
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorStructure_isPerfect
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorStructure_includeLeft_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorStructure_includeRight_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorFrobeniusEquiv_symm_tmul
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorStructure_algebraMap_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorStructure_lift_isDeltaHom

noncomputable section
universe u
open scoped TensorProduct
open SerrePositivity SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T))

-- No flatness, completeness, finiteness or nontriviality hypotheses.
example : (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).IsPerfect :=
  perfectDeltaTensorStructure_isPerfect p R S T DR DS DT hR hS hT hRS hRT

example : DS.IsDeltaHom
    (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT)
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom :=
  perfectDeltaTensorStructure_includeLeft_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT

example : DR.IsDeltaHom
    (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT)
    (algebraMap R (S ⊗[R] T)) :=
  perfectDeltaTensorStructure_algebraMap_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT

example (E : Type u) [CommRing E] (DE : DeltaStructure p E)
    (hpE : Function.Injective (fun x : E => (p : E) * x))
    (fS : S →+* E) (fT : T →+* E)
    (hMatch : ∀ r, fS (algebraMap R S r) = fT (algebraMap R T r))
    (hfS : DS.IsDeltaHom DE fS) (hfT : DT.IsDeltaHom DE fT) :
    (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).IsDeltaHom DE
      (coefficientTensorLift fS fT hMatch) :=
  perfectDeltaTensorStructure_lift_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT
    E DE hpE fS fT hMatch hfS hfT
