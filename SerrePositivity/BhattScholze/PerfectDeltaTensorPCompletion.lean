module

public import SerrePositivity.BhattScholze.PerfectDeltaTensorStructure
public import SerrePositivity.BhattScholze.PerfectDeltaPCompletion
/-! # The classical p-completion of a perfect delta tensor

The original completion unit and both factor maps preserve delta. Comparison
with the original derived completed tensor H0 is a separate theorem.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T))
local notation "B" => S ⊗[R] T
local notation "Cp" => AdicCompletion (Ideal.span {(p : B)}) B

/-- The classical p-completion inherits the tensor delta structure. -/
def perfectDeltaTensorPCompletionStructure : DeltaStructure p Cp :=
  (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).adicCompletion
    (Ideal.span {(p : B)}) (Ideal.mem_span_singleton_self _)

/-- The completed delta structure is perfect. -/
lemma perfectDeltaTensorPCompletionStructure_isPerfect :
    (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT).IsPerfect :=
  (perfectDeltaTensorStructure_isPerfect p R S T DR DS DT hR hS hT hRS hRT).adicCompletion_span_p

/-- The original completion unit preserves delta. -/
lemma perfectDeltaTensorPCompletionStructure_unit_isDeltaHom :
    (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).IsDeltaHom
      (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT)
      (algebraMap B Cp) :=
  (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).isDeltaHom_adicCompletion
    (Ideal.span {(p : B)}) (Ideal.mem_span_singleton_self _)

/-- The original completed left factor map preserves delta. -/
lemma perfectDeltaTensorPCompletionStructure_includeLeft_isDeltaHom :
    DS.IsDeltaHom (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT)
      ((algebraMap B Cp).comp
        (Algebra.TensorProduct.includeLeft : S →ₐ[R] B).toRingHom) :=
  (perfectDeltaTensorPCompletionStructure_unit_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT).comp
    (perfectDeltaTensorStructure_includeLeft_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT)

/-- The original completed right factor map preserves delta. -/
lemma perfectDeltaTensorPCompletionStructure_includeRight_isDeltaHom :
    DT.IsDeltaHom (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT)
      ((algebraMap B Cp).comp
        (Algebra.TensorProduct.includeRight : T →ₐ[R] B).toRingHom) :=
  (perfectDeltaTensorPCompletionStructure_unit_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT).comp
    (perfectDeltaTensorStructure_includeRight_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT)

/-- The original completed coefficient map preserves delta. -/
lemma perfectDeltaTensorPCompletionStructure_base_isDeltaHom :
    DR.IsDeltaHom (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT)
      ((algebraMap B Cp).comp (algebraMap R B)) :=
  (perfectDeltaTensorPCompletionStructure_unit_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT).comp
    (perfectDeltaTensorStructure_algebraMap_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT)
end SerrePositivity.BhattScholze
