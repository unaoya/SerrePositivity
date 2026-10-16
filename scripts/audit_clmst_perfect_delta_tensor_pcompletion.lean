import SerrePositivity.BhattScholze.PerfectDeltaTensorPCompletion
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorPCompletionStructure
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorPCompletionStructure_isPerfect
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorPCompletionStructure_unit_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorPCompletionStructure_includeLeft_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorPCompletionStructure_includeRight_isDeltaHom
assert_no_sorry SerrePositivity.BhattScholze.perfectDeltaTensorPCompletionStructure_base_isDeltaHom

#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorPCompletionStructure
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorPCompletionStructure_isPerfect
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorPCompletionStructure_unit_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorPCompletionStructure_includeLeft_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorPCompletionStructure_includeRight_isDeltaHom
#print axioms SerrePositivity.BhattScholze.perfectDeltaTensorPCompletionStructure_base_isDeltaHom

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
local notation "B" => S ⊗[R] T
local notation "Cp" => AdicCompletion (Ideal.span {(p : B)}) B

-- No completeness, nontriviality or flatness hypothesis is added to the delta diagram.
example : (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT).IsPerfect :=
  perfectDeltaTensorPCompletionStructure_isPerfect p R S T DR DS DT hR hS hT hRS hRT

example : (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).IsDeltaHom
    (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT)
    (algebraMap B Cp) :=
  perfectDeltaTensorPCompletionStructure_unit_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT

example : DR.IsDeltaHom
    (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT)
    ((algebraMap B Cp).comp (algebraMap R B)) :=
  perfectDeltaTensorPCompletionStructure_base_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT
