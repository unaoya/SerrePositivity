module

public import SerrePositivity.CommutativeAlgebra.CoprimeFactorLocalization
public import SerrePositivity.CommutativeAlgebra.LocalizedSurjectiveQuotient

/-! # The structural quotient map onto the cubic cyclotomic closed fiber -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open Polynomial IsLocalRing
variable {R : Type u} [CommRing R] [IsLocalRing R]
    (g h : (ResidueField R)[X])
    (hf : cubicCyclotomicPolynomial (ResidueField R) = g * h)

/-- The closed fiber written in the chosen factorization coordinates. -/
def cubicCyclotomicFiberMap : CubicCyclotomicAlgebra R →+* AdjoinRoot (g * h) :=
  AdjoinRoot.map (residue R) (cubicCyclotomicPolynomial R) (g * h)
    (by rw [cubicCyclotomicPolynomial_map_residue, hf])

lemma cubicCyclotomicFiberMap_surjective : Function.Surjective (cubicCyclotomicFiberMap g h hf) :=
  adjoinRoot_map_surjective _ residue_surjective _ _ _

/-- The polynomial quotient base-change comparison, with the factorization fixed. -/
def cubicCyclotomicClosedFiberEquiv :
    (CubicCyclotomicAlgebra R ⧸ (maximalIdeal R).map
      (algebraMap R (CubicCyclotomicAlgebra R))) ≃+* AdjoinRoot (g * h) :=
  (AdjoinRoot.quotEquivQuotMap (cubicCyclotomicPolynomial R) (maximalIdeal R)).toRingEquiv.trans
    (Ideal.quotEquivOfEq (by
      change Ideal.span ({(cubicCyclotomicPolynomial R).map (residue R)} :
        Set (ResidueField R)[X]) = Ideal.span {g * h}
      rw [cubicCyclotomicPolynomial_map_residue, hf]))

lemma cubicCyclotomicClosedFiberEquiv_comp :
    (cubicCyclotomicClosedFiberEquiv g h hf).toRingHom.comp (Ideal.Quotient.mk _) =
      cubicCyclotomicFiberMap g h hf := by
  apply RingHom.ext
  intro x
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  change cubicCyclotomicClosedFiberEquiv g h hf (Ideal.Quotient.mk _
    (AdjoinRoot.mk (cubicCyclotomicPolynomial R) q)) = _
  have he := AdjoinRoot.quotEquivQuotMap_apply_mk
    (cubicCyclotomicPolynomial R) q (maximalIdeal R)
  have he' := congrArg (Ideal.quotEquivOfEq (show
    Ideal.span ({(cubicCyclotomicPolynomial R).map (residue R)} :
      Set (ResidueField R)[X]) = Ideal.span {g * h} by
      rw [cubicCyclotomicPolynomial_map_residue, hf])) he
  have he'' : cubicCyclotomicClosedFiberEquiv g h hf (Ideal.Quotient.mk _
      (AdjoinRoot.mk (cubicCyclotomicPolynomial R) q)) =
      AdjoinRoot.mk (g * h) (q.map (residue R)) := by
    exact he'.trans (Ideal.quotEquivOfEq_mk _ _)
  exact he''.trans (adjoinRoot_map_mk (residue R) (cubicCyclotomicPolynomial R) (g * h) _ q).symm

lemma cubicCyclotomicFiberMap_ker :
    RingHom.ker (cubicCyclotomicFiberMap g h hf) =
      (maximalIdeal R).map (algebraMap R (CubicCyclotomicAlgebra R)) := by
  rw [← cubicCyclotomicClosedFiberEquiv_comp]
  ext x
  rw [RingHom.mem_ker, RingHom.comp_apply]
  rw [map_eq_zero_iff (cubicCyclotomicClosedFiberEquiv g h hf).toRingHom
      (cubicCyclotomicClosedFiberEquiv g h hf).injective,
    Ideal.Quotient.eq_zero_iff_mem]

end SerrePositivity
