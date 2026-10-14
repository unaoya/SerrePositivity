module

public import SerrePositivity.KTheory.Adams.KoszulSquareCoordinates

/-! # The positive Koszul summand inside the tensor square -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]

namespace Adams

abbrev oneKoszulSquarePositiveGenerator (a : R) :=
  oneKoszulSquareLeft a + oneKoszulSquareRight a

lemma oneKoszulSquarePositiveGenerator_d (a : R) :
    oneKoszulSquarePositiveGenerator a ≫ (tensorSquare (oneKoszulComplex a)).d (-1) 0 =
      (2 * a) • oneKoszulSquareBottom a := by
  rw [Preadditive.add_comp, oneKoszulSquareLeft_d, oneKoszulSquareRight_d]
  simp only [two_mul, add_smul]

def oneKoszulPositiveEmbeddingX (a : R) (n : ℤ) :
    (oneKoszulComplex (2 * a)).X n ⟶ (tensorSquare (oneKoszulComplex a)).X n :=
  if h : n = -1 then
    ((oneKoszulComplex (2 * a)).XIsoOfEq h).hom ≫ (oneKoszulXNegOneIso (2 * a)).hom ≫
      oneKoszulSquarePositiveGenerator a ≫ ((tensorSquare (oneKoszulComplex a)).XIsoOfEq h).inv
  else if h : n = 0 then
    ((oneKoszulComplex (2 * a)).XIsoOfEq h).hom ≫ (oneKoszulXZeroIso (2 * a)).hom ≫
      oneKoszulSquareBottom a ≫ ((tensorSquare (oneKoszulComplex a)).XIsoOfEq h).inv
  else 0

@[simp]
lemma oneKoszulPositiveEmbeddingX_neg_one (a : R) :
    oneKoszulPositiveEmbeddingX a (-1) =
      (oneKoszulXNegOneIso (2 * a)).hom ≫ oneKoszulSquarePositiveGenerator a := by
  simp [oneKoszulPositiveEmbeddingX]

@[simp]
lemma oneKoszulPositiveEmbeddingX_zero (a : R) :
    oneKoszulPositiveEmbeddingX a 0 =
      (oneKoszulXZeroIso (2 * a)).hom ≫ oneKoszulSquareBottom a := by
  simp [oneKoszulPositiveEmbeddingX]

lemma oneKoszulPositiveEmbeddingX_comm (a : R) (n m : ℤ) (h : n + 1 = m) :
    oneKoszulPositiveEmbeddingX a n ≫ (tensorSquare (oneKoszulComplex a)).d n m =
      (oneKoszulComplex (2 * a)).d n m ≫ oneKoszulPositiveEmbeddingX a m := by
  subst m
  by_cases hn : n = -1
  · subst n
    apply (cancel_epi (oneKoszulXNegOneIso (2 * a)).inv).mp
    simp only [Int.reduceNeg, Int.reduceAdd, oneKoszulPositiveEmbeddingX_neg_one,
      oneKoszulPositiveEmbeddingX_zero, Category.assoc, Iso.inv_hom_id_assoc]
    rw [oneKoszulSquarePositiveGenerator_d,
      ← Category.assoc (oneKoszulXNegOneIso (2 * a)).inv,
      oneKoszul_generator_d]
    simp [Linear.smul_comp]
  · by_cases hn0 : n = 0
    · subst n
      exact (oneKoszulSquare_isZero_X_other a 1 (by omega)).eq_of_tgt _ _
    · exact (oneKoszul_isZero_X_other (2 * a) n ⟨hn, hn0⟩).eq_of_src _ _

def oneKoszulPositiveEmbedding (a : R) :
    oneKoszulComplex (2 * a) ⟶ tensorSquare (oneKoszulComplex a) where
  f := oneKoszulPositiveEmbeddingX a
  comm' n m h := oneKoszulPositiveEmbeddingX_comm a n m h

@[reassoc]
lemma oneKoszulPositiveEmbedding_swap (a : R) :
    oneKoszulPositiveEmbedding a ≫ tensorSquareSwap (oneKoszulComplex a) =
      oneKoszulPositiveEmbedding a := by
  apply HomologicalComplex.Hom.ext
  funext n
  change oneKoszulPositiveEmbeddingX a n ≫ (tensorSquareSwap (oneKoszulComplex a)).f n =
    oneKoszulPositiveEmbeddingX a n
  by_cases hn : n = -1
  · subst n
    rw [oneKoszulPositiveEmbeddingX_neg_one, Category.assoc, oneKoszulSquarePositive_swap]
  · by_cases hn0 : n = 0
    · subst n
      simp [Category.assoc, oneKoszulSquareBottom_swap]
    · exact (oneKoszul_isZero_X_other (2 * a) n ⟨hn, hn0⟩).eq_of_src _ _

variable [Invertible (2 : R)]

lemma oneKoszulPositiveEmbedding_projector (a : R) :
    oneKoszulPositiveEmbedding a ≫ (tensorSquarePositiveProjector (oneKoszulComplex a)).map =
      oneKoszulPositiveEmbedding a := by
  rw [tensorSquarePositiveProjector_map, Linear.comp_smul, Preadditive.comp_add,
    Category.comp_id, oneKoszulPositiveEmbedding_swap, ← two_smul R,
    smul_smul, invOf_mul_self, one_smul]

def oneKoszulPositiveImageEmbedding (a : R) :
    oneKoszulComplex (2 * a) ⟶ tensorSquarePositive (oneKoszulComplex a) :=
  oneKoszulPositiveEmbedding a ≫ (tensorSquarePositiveProjector (oneKoszulComplex a)).projection

@[reassoc]
lemma oneKoszulPositiveImageEmbedding_inclusion (a : R) :
    oneKoszulPositiveImageEmbedding a ≫
      (tensorSquarePositiveProjector (oneKoszulComplex a)).inclusion =
    oneKoszulPositiveEmbedding a := by
  rw [oneKoszulPositiveImageEmbedding, Category.assoc,
    CochainIdempotent.projection_inclusion, oneKoszulPositiveEmbedding_projector]

end Adams
end SerrePositivity
