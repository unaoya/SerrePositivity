module

public import SerrePositivity.HomologicalAlgebra.TorDimensionShift
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # The actual standard Tor₁(R/I,R/I) and the existing conormal module I/I² -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory TensorProduct
variable (R : Type u) [CommRing R] (I : Ideal R)

/-- The inclusion of I tensors to zero over its own quotient. -/
lemma idealSubtype_lTensor_quotient_eq_zero : I.subtype.lTensor (R ⧸ I) = 0 := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro q
  apply LinearMap.ext
  intro x
  apply (TensorProduct.rid R (R ⧸ I)).injective
  change (x : R) • q = 0
  change Ideal.Quotient.mk I (x : R) * q = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property, zero_mul]

/-- The original standard Tor₁, computed from 0→I→R→R/I→0, is the actual conormal. -/
def quotientTorOneConormalEquiv : TorModule R 1 (R ⧸ I) (R ⧸ I) ≃ₗ[R] I.Cotangent := by
  have he : Function.Exact I.subtype I.mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]
  have h₂ : Subsingleton (TorModule R 1 (R ⧸ I) R) :=
    ModuleCat.subsingleton_of_isZero (isZero_Tor_succ_of_projective
      (ModuleCat.{u} R) (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R R) 0)
  let e := Classical.choice (nonempty_torModule_one_equiv_ker (R ⧸ I) I.subtype I.mkQ
    I.subtype_injective I.mkQ_surjective he h₂)
  let k : LinearMap.ker (I.subtype.lTensor (R ⧸ I)) ≃ₗ[R] ((R ⧸ I) ⊗[R] I) :=
    LinearEquiv.ofBijective (LinearMap.ker (I.subtype.lTensor (R ⧸ I))).subtype
      ⟨Submodule.subtype_injective _, fun x =>
        ⟨⟨x, by rw [idealSubtype_lTensor_quotient_eq_zero]; rfl⟩, rfl⟩⟩
  exact e.trans (k.trans (TensorProduct.quotTensorEquivQuotSMul I I))

/-- Scalar surjectivity is preserved under the original Tor₁/conormal comparison. -/
lemma quotientTorOne_smul_surjective_iff_conormal (a : R) :
    Function.Surjective (fun x : TorModule R 1 (R ⧸ I) (R ⧸ I) => a • x) ↔
      Function.Surjective (fun x : I.Cotangent => a • x) := by
  let e := quotientTorOneConormalEquiv R I
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := h (e.symm x)
    refine ⟨e y, ?_⟩
    change a • e y = x
    change a • y = e.symm x at hy
    rw [← e.map_smul, hy, e.apply_symm_apply]
  · intro h x
    obtain ⟨y, hy⟩ := h (e x)
    refine ⟨e.symm y, ?_⟩
    change a • e.symm y = x
    change a • y = e x at hy
    rw [← e.symm.map_smul, hy, e.symm_apply_apply]

/-- Ordinary self-Tor₁ vanishing is exactly idempotence of the actual ideal. -/
lemma quotientTorOne_subsingleton_iff_idempotent :
    Subsingleton (TorModule R 1 (R ⧸ I) (R ⧸ I)) ↔ IsIdempotentElem I := by
  let e := quotientTorOneConormalEquiv R I
  constructor
  · intro h
    letI := h
    apply I.cotangent_subsingleton_iff.mp
    exact ⟨fun x y => e.symm.injective (Subsingleton.elim _ _)⟩
  · intro h
    letI := I.cotangent_subsingleton_iff.mpr h
    exact ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

end SerrePositivity
