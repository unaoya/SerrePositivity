module

public import SerrePositivity.KTheory.Adams.KoszulShiftOneModel

/-! # The negative shifted Koszul summand inside the tensor square -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]
namespace Adams

def oneKoszulNegativeEmbeddingX (a : R) (n : ℤ) :
    (oneKoszulShiftOne a).X n ⟶ (tensorSquare (oneKoszulComplex a)).X n :=
  if h : n = -2 then
    ((oneKoszulShiftOne a).XIsoOfEq h).hom ≫ (oneKoszulShiftOneXNegTwoIso a).hom ≫
      oneKoszulSquareTop a ≫ ((tensorSquare (oneKoszulComplex a)).XIsoOfEq h).inv
  else if h : n = -1 then
    ((oneKoszulShiftOne a).XIsoOfEq h).hom ≫ (oneKoszulShiftOneXNegOneIso a).hom ≫
      oneKoszulSquareNegativeGenerator a ≫ ((tensorSquare (oneKoszulComplex a)).XIsoOfEq h).inv
  else 0

@[simp]
lemma oneKoszulNegativeEmbeddingX_neg_two (a : R) :
    oneKoszulNegativeEmbeddingX a (-2) =
      (oneKoszulShiftOneXNegTwoIso a).hom ≫ oneKoszulSquareTop a := by
  simp [oneKoszulNegativeEmbeddingX]

@[simp]
lemma oneKoszulNegativeEmbeddingX_neg_one (a : R) :
    oneKoszulNegativeEmbeddingX a (-1) =
      (oneKoszulShiftOneXNegOneIso a).hom ≫ oneKoszulSquareNegativeGenerator a := by
  simp [oneKoszulNegativeEmbeddingX]

lemma oneKoszulNegativeEmbeddingX_comm (a : R) (n m : ℤ) (h : n + 1 = m) :
    oneKoszulNegativeEmbeddingX a n ≫ (tensorSquare (oneKoszulComplex a)).d n m =
      (oneKoszulShiftOne a).d n m ≫ oneKoszulNegativeEmbeddingX a m := by
  subst m
  by_cases hn2 : n = -2
  · subst n
    apply (cancel_epi (oneKoszulShiftOneXNegTwoIso a).inv).mp
    simp only [Int.reduceNeg, Int.reduceAdd, oneKoszulNegativeEmbeddingX_neg_two,
      oneKoszulNegativeEmbeddingX_neg_one, Category.assoc, Iso.inv_hom_id_assoc]
    rw [oneKoszulSquareTop_d_negative,
      ← Category.assoc (oneKoszulShiftOneXNegTwoIso a).inv,
      oneKoszulShiftOne_generator_d]
    simp [Linear.smul_comp, oneKoszulSquareNegativeGenerator,
      sub_eq_add_neg, add_comm]
  · by_cases hn1 : n = -1
    · subst n
      have hd : (oneKoszulShiftOne a).d (-1) 0 = 0 :=
        (oneKoszulShiftOne_isZero_X_other a 0 (by omega)).eq_of_tgt _ _
      change oneKoszulNegativeEmbeddingX a (-1) ≫
        (tensorSquare (oneKoszulComplex a)).d (-1) 0 =
        (oneKoszulShiftOne a).d (-1) 0 ≫ oneKoszulNegativeEmbeddingX a 0
      rw [hd, zero_comp, oneKoszulNegativeEmbeddingX_neg_one, Category.assoc,
        oneKoszulSquareNegativeGenerator_d, comp_zero]
    · exact (oneKoszulShiftOne_isZero_X_other a n ⟨hn2, hn1⟩).eq_of_src _ _

def oneKoszulNegativeEmbedding (a : R) :
    oneKoszulShiftOne a ⟶ tensorSquare (oneKoszulComplex a) where
  f := oneKoszulNegativeEmbeddingX a
  comm' n m h := oneKoszulNegativeEmbeddingX_comm a n m h

@[reassoc]
lemma oneKoszulNegativeEmbedding_swap (a : R) :
    oneKoszulNegativeEmbedding a ≫ tensorSquareSwap (oneKoszulComplex a) =
      -oneKoszulNegativeEmbedding a := by
  apply HomologicalComplex.Hom.ext
  funext n
  change oneKoszulNegativeEmbeddingX a n ≫ (tensorSquareSwap (oneKoszulComplex a)).f n =
    -oneKoszulNegativeEmbeddingX a n
  by_cases hn2 : n = -2
  · subst n
    rw [oneKoszulNegativeEmbeddingX_neg_two, Category.assoc, oneKoszulSquareTop_swap,
      Preadditive.comp_neg]
  · by_cases hn1 : n = -1
    · subst n
      rw [oneKoszulNegativeEmbeddingX_neg_one, Category.assoc,
        oneKoszulSquareNegative_swap, Preadditive.comp_neg]
    · exact (oneKoszulShiftOne_isZero_X_other a n ⟨hn2, hn1⟩).eq_of_src _ _

variable [Invertible (2 : R)]

lemma oneKoszulNegativeEmbedding_projector (a : R) :
    oneKoszulNegativeEmbedding a ≫ (tensorSquareNegativeProjector (oneKoszulComplex a)).map =
      oneKoszulNegativeEmbedding a := by
  rw [tensorSquareNegativeProjector_map, Linear.comp_smul, Preadditive.comp_sub,
    Category.comp_id, oneKoszulNegativeEmbedding_swap, sub_neg_eq_add,
    ← two_smul R, smul_smul, invOf_mul_self, one_smul]

def oneKoszulNegativeImageEmbedding (a : R) :
    oneKoszulShiftOne a ⟶ tensorSquareNegative (oneKoszulComplex a) :=
  oneKoszulNegativeEmbedding a ≫ (tensorSquareNegativeProjector (oneKoszulComplex a)).projection

@[reassoc]
lemma oneKoszulNegativeImageEmbedding_inclusion (a : R) :
    oneKoszulNegativeImageEmbedding a ≫
      (tensorSquareNegativeProjector (oneKoszulComplex a)).inclusion =
    oneKoszulNegativeEmbedding a := by
  rw [oneKoszulNegativeImageEmbedding, Category.assoc,
    CochainIdempotent.projection_inclusion, oneKoszulNegativeEmbedding_projector]

end Adams
end SerrePositivity
