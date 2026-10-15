module

public import SerrePositivity.HomologicalAlgebra.CochainTensorTriple

/-! # Differentials on homogeneous two- and three-factor tensors -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

lemma cochainTensorTripleι_apply_of_sum (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k s n : ℤ) (hs : i + j = s) (h : s + k = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    cochainTensorTripleι P Q T i j k n (by omega) ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
      ιTensorObj (cochainTensor P Q) T s k n h
        (ιTensorObj P Q i j s hs (x ⊗ₜ[R] y) ⊗ₜ[R] z) := by
  subst hs
  rfl

lemma cochainTensorTriple_d_apply_ι (P Q T : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k n : ℤ) (h : i + j + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (cochainTensor (cochainTensor P Q) T).d n (n + 1)
        (cochainTensorTripleι P Q T i j k n h ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      cochainTensorTripleι P Q T (i + 1) j k (n + 1) (by omega)
        ((P.d i (i + 1) x ⊗ₜ[R] y) ⊗ₜ[R] z) +
      i.negOnePow • cochainTensorTripleι P Q T i (j + 1) k (n + 1) (by omega)
        ((x ⊗ₜ[R] Q.d j (j + 1) y) ⊗ₜ[R] z) +
      (i + j).negOnePow • cochainTensorTripleι P Q T i j (k + 1) (n + 1) (by omega)
        ((x ⊗ₜ[R] y) ⊗ₜ[R] T.d k (k + 1) z) := by
  rw [cochainTensorTripleι_apply, cochainTensor_d_apply_ι, cochainTensor_d_apply_ι]
  simp only [TensorProduct.add_tmul, map_add, Units.smul_def,
    ← TensorProduct.smul_tmul', map_zsmul]
  rw [cochainTensorTripleι_apply_of_sum P Q T (i + 1) j k (i + j + 1) (n + 1)
    (by omega) (by omega),
    cochainTensorTripleι_apply_of_sum P Q T i (j + 1) k (i + j + 1) (n + 1)
      (by omega) (by omega), cochainTensorTripleι_apply]


end SerrePositivity
