module

public import SerrePositivity.CommutativeAlgebra.CoefficientTensorAutomorphism
public import SerrePositivity.BhattScholze.Prism.Tensor.PerfectDeltaTensorRegular
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.Algebra.CharP.Lemmas
/-! # A perfect delta structure on the original ordinary tensor

Both algebra maps are delta maps. The factor Frobenius automorphisms give the
specified semilinear tensor automorphism, which is a Frobenius lift modulo p.
The already proved p-regularity then reconstructs the unique delta structure
with that lift. Zero tensor rings are included without CharP instances.
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

/-- The factor Frobenius maps induce an automorphism with its original coefficient action. -/
def perfectDeltaTensorFrobeniusEquiv : S ⊗[R] T ≃+* S ⊗[R] T :=
  coefficientTensorAutomorphism (DR.frobeniusEquiv hR) (DS.frobeniusEquiv hS)
    (DT.frobeniusEquiv hT) (fun r => (hRS.map_frobeniusLift r).symm)
    (fun r => (hRT.map_frobeniusLift r).symm)

/-- The tensor Frobenius acts factorwise on pure tensors. -/
lemma perfectDeltaTensorFrobeniusEquiv_tmul (s : S) (t : T) :
    perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT (s ⊗ₜ[R] t) =
      DS.frobeniusLift s ⊗ₜ[R] DT.frobeniusLift t :=
  coefficientTensorAutomorphism_tmul ..

/-- Reduction modulo p is the p-th power map, including zero quotients. -/
lemma perfectDeltaTensorFrobeniusEquiv_mod_p (x : S ⊗[R] T) :
    Ideal.Quotient.mk (Ideal.span {(p : S ⊗[R] T)})
        (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT x) =
      Ideal.Quotient.mk (Ideal.span {(p : S ⊗[R] T)}) x ^ p := by
  let B := S ⊗[R] T
  let q := Ideal.Quotient.mk (Ideal.span {(p : B)})
  let iS := (Algebra.TensorProduct.includeLeft : S →ₐ[R] B).toRingHom
  let iT := (Algebra.TensorProduct.includeRight : T →ₐ[R] B).toRingHom
  have hpq : q (p : B) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hqp : (p : B ⧸ Ideal.span {(p : B)}) = 0 := by
    rw [← map_natCast q, hpq]
  have hpS : (q.comp iS) (p : S) = 0 := by rw [RingHom.comp_apply, map_natCast, hpq]
  have hpT : (q.comp iT) (p : T) = 0 := by rw [RingHom.comp_apply, map_natCast, hpq]
  have hmodS := DS.map_frobeniusLift_of_map_p_eq_zero (q.comp iS) hpS
  have hmodT := DT.map_frobeniusLift_of_map_p_eq_zero (q.comp iT) hpT
  have hprod (s : S) (t : T) : iS s * iT t = s ⊗ₜ[R] t := by
    change (s ⊗ₜ[R] (1 : T)) * ((1 : S) ⊗ₜ[R] t) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  induction x using TensorProduct.inductionOn with
  | tmul s t =>
    rw [perfectDeltaTensorFrobeniusEquiv_tmul]
    change q (DS.frobeniusLift s ⊗ₜ[R] DT.frobeniusLift t) = q (s ⊗ₜ[R] t) ^ p
    rw [← hprod, ← hprod, map_mul, map_mul, mul_pow]
    exact congrArg₂ (fun x y => x * y) (hmodS s) (hmodT t)
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    have h := add_pow_prime_eq (Fact.out : p.Prime) (q x) (q y)
    simpa only [hqp, zero_mul, add_zero] using h.symm

/-- The original ordinary tensor carries the reconstructed delta structure. -/
def perfectDeltaTensorStructure : DeltaStructure p (S ⊗[R] T) :=
  (DeltaStructure.existsUnique_of_mod_p
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
    (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT).toRingHom
    (perfectDeltaTensorFrobeniusEquiv_mod_p p R S T DR DS DT hR hS hT hRS hRT)).choose

/-- Its Frobenius lift is the specified tensor automorphism. -/
lemma perfectDeltaTensorStructure_frobeniusLift :
    (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).frobeniusLift =
      (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT).toRingHom :=
  (DeltaStructure.existsUnique_of_mod_p
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
    (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT).toRingHom
    (perfectDeltaTensorFrobeniusEquiv_mod_p p R S T DR DS DT hR hS hT hRS hRT)).choose_spec.1

/-- The reconstructed tensor delta structure is perfect. -/
lemma perfectDeltaTensorStructure_isPerfect :
    (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).IsPerfect := by
  rw [DeltaStructure.IsPerfect, perfectDeltaTensorStructure_frobeniusLift]
  exact (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT).bijective

/-- The standard inclusion of the left factor preserves delta. -/
lemma perfectDeltaTensorStructure_includeLeft_isDeltaHom :
    DS.IsDeltaHom (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT)
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
  intro s
  rw [perfectDeltaTensorStructure_frobeniusLift]
  change DS.frobeniusLift s ⊗ₜ[R] (1 : T) =
    perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT (s ⊗ₜ[R] (1 : T))
  rw [perfectDeltaTensorFrobeniusEquiv_tmul, map_one]

/-- The standard inclusion of the right factor preserves delta. -/
lemma perfectDeltaTensorStructure_includeRight_isDeltaHom :
    DT.IsDeltaHom (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT)
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
  intro t
  rw [perfectDeltaTensorStructure_frobeniusLift]
  change (1 : S) ⊗ₜ[R] DT.frobeniusLift t =
    perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT ((1 : S) ⊗ₜ[R] t)
  rw [perfectDeltaTensorFrobeniusEquiv_tmul, map_one]

/-- The inverse tensor Frobenius acts by inverse factor Frobenius maps. -/
lemma perfectDeltaTensorFrobeniusEquiv_symm_tmul (s : S) (t : T) :
    (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT).symm (s ⊗ₜ[R] t) =
      (DS.frobeniusEquiv hS).symm s ⊗ₜ[R] (DT.frobeniusEquiv hT).symm t :=
  coefficientTensorAutomorphism_symm_tmul ..

/-- The original base algebra map preserves delta. -/
lemma perfectDeltaTensorStructure_algebraMap_isDeltaHom :
    DR.IsDeltaHom (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT)
      (algebraMap R (S ⊗[R] T)) := by
  have h := (perfectDeltaTensorStructure_includeLeft_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT).comp hRS
  have he : (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom.comp
      (algebraMap R S) = algebraMap R (S ⊗[R] T) := by
    ext r
    exact (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).commutes r
  rwa [he] at h

/-- The ordinary tensor lift preserves delta into any p-regular delta target. -/
lemma perfectDeltaTensorStructure_lift_isDeltaHom
    (E : Type u) [CommRing E] (DE : DeltaStructure p E)
    (hpE : Function.Injective (fun x : E => (p : E) * x))
    (fS : S →+* E) (fT : T →+* E)
    (hMatch : ∀ r, fS (algebraMap R S r) = fT (algebraMap R T r))
    (hfS : DS.IsDeltaHom DE fS) (hfT : DT.IsDeltaHom DE fT) :
    (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).IsDeltaHom DE
      (coefficientTensorLift fS fT hMatch) := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _ hpE
  intro x
  rw [perfectDeltaTensorStructure_frobeniusLift]
  induction x using TensorProduct.inductionOn with
  | tmul s t =>
    change coefficientTensorLift fS fT hMatch
      (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT (s ⊗ₜ[R] t)) = _
    rw [perfectDeltaTensorFrobeniusEquiv_tmul, coefficientTensorLift_tmul,
      coefficientTensorLift_tmul, map_mul, hfS.map_frobeniusLift, hfT.map_frobeniusLift]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
end SerrePositivity.BhattScholze
