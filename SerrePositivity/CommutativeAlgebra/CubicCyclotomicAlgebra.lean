module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Tactic.Ring

/-! # The quadratic algebra adjoining a cube root of unity -/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open Polynomial IsLocalRing Module
variable (R : Type u) [CommRing R]

/-- The third cyclotomic polynomial, used without a generic cyclotomic algebra theory. -/
def cubicCyclotomicPolynomial : R[X] := X ^ 2 + X + 1

lemma cubicCyclotomicPolynomial_monic : (cubicCyclotomicPolynomial R).Monic := by
  nontriviality R
  simpa only [cubicCyclotomicPolynomial, add_assoc, C_1] using
    (monic_X_pow_add (p := (X + C (1 : R))) (n := 2)
      (by rw [degree_X_add_C]; norm_num))

lemma cubicCyclotomicPolynomial_natDegree [Nontrivial R] :
    (cubicCyclotomicPolynomial R).natDegree = 2 := by
  rw [cubicCyclotomicPolynomial, add_assoc,
    natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · rw [← C_1, natDegree_X_add_C]
    simp

abbrev CubicCyclotomicAlgebra := AdjoinRoot (cubicCyclotomicPolynomial R)

instance cubicCyclotomicAlgebra_nontrivial [Nontrivial R] :
    Nontrivial (CubicCyclotomicAlgebra R) := by
  apply (AdjoinRoot.nontrivial_iff_of_monic (cubicCyclotomicPolynomial_monic R)).mpr
  rw [degree_eq_natDegree (cubicCyclotomicPolynomial_monic R).ne_zero,
    cubicCyclotomicPolynomial_natDegree R]
  norm_num

def cubicCyclotomicRoot : CubicCyclotomicAlgebra R :=
  AdjoinRoot.root (cubicCyclotomicPolynomial R)

/-- The explicit two-element power basis of the quadratic algebra. -/
def cubicCyclotomicBasis [Nontrivial R] : Basis (Fin 2) R (CubicCyclotomicAlgebra R) :=
  (AdjoinRoot.powerBasis' (cubicCyclotomicPolynomial_monic R)).basis.reindex
    (finCongr (cubicCyclotomicPolynomial_natDegree R))

lemma cubicCyclotomicBasis_apply [Nontrivial R] (i : Fin 2) :
    cubicCyclotomicBasis R i = cubicCyclotomicRoot R ^ (i : ℕ) := by
  rw [cubicCyclotomicBasis, Basis.reindex_apply]
  exact (AdjoinRoot.powerBasis' (cubicCyclotomicPolynomial_monic R)).basis_eq_pow _

instance cubicCyclotomicAlgebra_free : Module.Free R (CubicCyclotomicAlgebra R) :=
  (cubicCyclotomicPolynomial_monic R).free_adjoinRoot

instance cubicCyclotomicAlgebra_finite : Module.Finite R (CubicCyclotomicAlgebra R) :=
  (cubicCyclotomicPolynomial_monic R).finite_adjoinRoot

instance cubicCyclotomicAlgebra_flat : Module.Flat R (CubicCyclotomicAlgebra R) :=
  Module.Flat.of_free

lemma cubicCyclotomicRoot_relation :
    cubicCyclotomicRoot R ^ 2 + cubicCyclotomicRoot R + 1 = 0 := by
  have h := AdjoinRoot.eval₂_root (cubicCyclotomicPolynomial R)
  change (X ^ 2 + X + 1 : R[X]).eval₂
    (AdjoinRoot.of (cubicCyclotomicPolynomial R)) (cubicCyclotomicRoot R) = 0 at h
  rw [eval₂_add, eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
  exact h

variable {R}

/-- The defining relation implies the cube-root equation in every commutative ring. -/
lemma cube_eq_one_of_cubic_relation (t : R) (ht : t ^ 2 + t + 1 = 0) : t ^ 3 = 1 := by
  calc
    t ^ 3 = (t - 1) * (t ^ 2 + t + 1) + 1 := by ring
    _ = 1 := by rw [ht]; ring

/-- The two differences from 1 multiply to 3, also in mixed characteristic. -/
lemma one_sub_mul_one_sub_sq_of_cubic_relation (t : R) (ht : t ^ 2 + t + 1 = 0) :
    (1 - t) * (1 - t ^ 2) = 3 := by
  have hc := cube_eq_one_of_cubic_relation t ht
  calc
    (1 - t) * (1 - t ^ 2) = t ^ 3 + 2 - (t ^ 2 + t + 1) := by ring
    _ = 3 := by rw [hc, ht]; ring

lemma isUnit_three_of_residue_two_eq_zero [IsLocalRing R]
    (h : (2 : ResidueField R) = 0) : IsUnit (3 : R) := by
  apply (residue_ne_zero_iff_isUnit (3 : R)).mp
  have he : (3 : ResidueField R) = 1 := by
    calc
      (3 : ResidueField R) = 2 + 1 := by norm_num
      _ = 1 := by rw [h]; simp
  simpa only [map_ofNat, he] using (one_ne_zero : (1 : ResidueField R) ≠ 0)

lemma isUnit_one_sub_of_cubic_relation (t : R) (ht : t ^ 2 + t + 1 = 0)
    (hthree : IsUnit (3 : R)) : IsUnit (1 - t) ∧ IsUnit (1 - t ^ 2) := by
  have hm : IsUnit ((1 - t) * (1 - t ^ 2)) :=
    (one_sub_mul_one_sub_sq_of_cubic_relation t ht).symm ▸ hthree
  exact ⟨isUnit_of_mul_isUnit_left hm, isUnit_of_mul_isUnit_right hm⟩

lemma cubicCyclotomicRoot_cube : cubicCyclotomicRoot R ^ 3 = 1 :=
  cube_eq_one_of_cubic_relation _ (cubicCyclotomicRoot_relation R)

lemma cubicCyclotomicRoot_units_of_residue_two_eq_zero [IsLocalRing R]
    (h : (2 : ResidueField R) = 0) :
    IsUnit (1 - cubicCyclotomicRoot R) ∧ IsUnit (1 - cubicCyclotomicRoot R ^ 2) := by
  have hthree : IsUnit (3 : CubicCyclotomicAlgebra R) := by
    simpa only [map_ofNat] using
      (isUnit_three_of_residue_two_eq_zero h).map (algebraMap R (CubicCyclotomicAlgebra R))
  exact isUnit_one_sub_of_cubic_relation _ (cubicCyclotomicRoot_relation R) hthree

end SerrePositivity
