module
public import SerrePositivity.HomologicalAlgebra.CochainTensor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Separate lower and upper bounds for cochain tensor products -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- A tensor summand is zero when its left factor is zero. -/
lemma cochainTensorSummand_isZero_left (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n}) (h : IsZero (P.X ij.val.1)) :
    IsZero (cochainTensorSummand P Q n ij) := by
  exact (tensorRight (Q.X ij.val.2)).map_isZero h

/-- A tensor summand is zero when its right factor is zero. -/
lemma cochainTensorSummand_isZero_right (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n}) (h : IsZero (Q.X ij.val.2)) :
    IsZero (cochainTensorSummand P Q n ij) := by
  exact (tensorLeft (P.X ij.val.1)).map_isZero h

/-- A degree vanishes when each homogeneous summand has a zero factor. -/
lemma cochainTensor_isZero_X_of_summands
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (h : ∀ i j : ℤ, i + j = n → IsZero (P.X i) ∨ IsZero (Q.X j)) :
    IsZero ((cochainTensor P Q).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply mapBifunctor.hom_ext
  intro i j hij
  rcases h i j hij with hi | hj
  · exact ((tensorRight (Q.X j)).map_isZero hi).eq_of_src _ _
  · exact ((tensorLeft (P.X i)).map_isZero hj).eq_of_src _ _

/-- Upper bounds add without imposing any lower bounds. -/
lemma cochainTensor_isStrictlyLE
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [P.IsStrictlyLE a] [Q.IsStrictlyLE b] : (cochainTensor P Q).IsStrictlyLE (a + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  apply cochainTensor_isZero_X_of_summands
  intro i j hij
  by_cases hi : a < i
  · exact Or.inl (P.isZero_of_isStrictlyLE a i hi)
  · exact Or.inr (Q.isZero_of_isStrictlyLE b j (by omega))

/-- Lower bounds add without imposing any upper bounds. -/
lemma cochainTensor_isStrictlyGE
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [Q.IsStrictlyGE b] : (cochainTensor P Q).IsStrictlyGE (a + b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  apply cochainTensor_isZero_X_of_summands
  intro i j hij
  by_cases hi : i < a
  · exact Or.inl (P.isZero_of_isStrictlyGE a i hi)
  · exact Or.inr (Q.isZero_of_isStrictlyGE b j (by omega))

end SerrePositivity
