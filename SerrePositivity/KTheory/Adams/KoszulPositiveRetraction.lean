module

public import SerrePositivity.KTheory.Adams.KoszulSquareDual

/-! # A chain retraction onto the positive Koszul summand -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R] [Invertible (2 : R)]
namespace Adams

abbrev oneKoszulSquarePositiveDual (a : R) :=
  (⅟(2 : R)) • (oneKoszulSquareLeftDual a + oneKoszulSquareRightDual a)

@[reassoc (attr := simp)]
lemma oneKoszulSquareLeft_positiveDual (a : R) :
    oneKoszulSquareLeft a ≫ oneKoszulSquarePositiveDual a = (⅟(2 : R)) • 𝟙 _ := by
  simp [oneKoszulSquarePositiveDual, Linear.comp_smul]

@[reassoc (attr := simp)]
lemma oneKoszulSquareRight_positiveDual (a : R) :
    oneKoszulSquareRight a ≫ oneKoszulSquarePositiveDual a = (⅟(2 : R)) • 𝟙 _ := by
  simp [oneKoszulSquarePositiveDual, Linear.comp_smul]

@[reassoc]
lemma oneKoszulSquarePositiveGenerator_dual (a : R) :
    oneKoszulSquarePositiveGenerator a ≫ oneKoszulSquarePositiveDual a = 𝟙 _ := by
  rw [Preadditive.add_comp, oneKoszulSquareLeft_positiveDual,
    oneKoszulSquareRight_positiveDual, ← two_smul R, smul_smul]
  simp

def oneKoszulPositiveRetractionX (a : R) (n : ℤ) :
    (tensorSquare (oneKoszulComplex a)).X n ⟶ (oneKoszulComplex (2 * a)).X n :=
  if h : n = -1 then
    ((tensorSquare (oneKoszulComplex a)).XIsoOfEq h).hom ≫ oneKoszulSquarePositiveDual a ≫
      (oneKoszulXNegOneIso (2 * a)).inv ≫ ((oneKoszulComplex (2 * a)).XIsoOfEq h).inv
  else if h : n = 0 then
    ((tensorSquare (oneKoszulComplex a)).XIsoOfEq h).hom ≫ oneKoszulSquareBottomDual a ≫
      (oneKoszulXZeroIso (2 * a)).inv ≫ ((oneKoszulComplex (2 * a)).XIsoOfEq h).inv
  else 0

@[simp]
lemma oneKoszulPositiveRetractionX_neg_one (a : R) :
    oneKoszulPositiveRetractionX a (-1) =
      oneKoszulSquarePositiveDual a ≫ (oneKoszulXNegOneIso (2 * a)).inv := by
  simp [oneKoszulPositiveRetractionX]

@[simp]
lemma oneKoszulPositiveRetractionX_zero (a : R) :
    oneKoszulPositiveRetractionX a 0 =
      oneKoszulSquareBottomDual a ≫ (oneKoszulXZeroIso (2 * a)).inv := by
  simp [oneKoszulPositiveRetractionX]

lemma oneKoszulPositiveRetractionX_comm (a : R) (n m : ℤ) (h : n + 1 = m) :
    oneKoszulPositiveRetractionX a n ≫ (oneKoszulComplex (2 * a)).d n m =
      (tensorSquare (oneKoszulComplex a)).d n m ≫ oneKoszulPositiveRetractionX a m := by
  subst m
  have htwo : (2 : R) * a * ⅟(2 : R) = a := by
    rw [mul_comm (2 : R) a, mul_assoc, mul_invOf_self, mul_one]
  by_cases hn2 : n = -2
  · subst n
    apply oneKoszulSquareXNegTwo_hom_ext a
    have hz : oneKoszulPositiveRetractionX a (-2) = 0 := by
      simp [oneKoszulPositiveRetractionX]
    change oneKoszulSquareTop a ≫ oneKoszulPositiveRetractionX a (-2) ≫
        (oneKoszulComplex (2 * a)).d (-2) (-1) =
      oneKoszulSquareTop a ≫ (tensorSquare (oneKoszulComplex a)).d (-2) (-1) ≫
        oneKoszulPositiveRetractionX a (-1)
    rw [hz, zero_comp, comp_zero, oneKoszulPositiveRetractionX_neg_one,
      ← Category.assoc (oneKoszulSquareTop a) ((tensorSquare (oneKoszulComplex a)).d (-2) (-1)),
      oneKoszulSquareTop_d]
    simp [Preadditive.sub_comp, Linear.smul_comp, Category.assoc]
  · by_cases hn : n = -1
    · subst n
      apply oneKoszulSquareXNegOne_hom_ext a
      all_goals
        simp only [Int.reduceNeg, Int.reduceAdd, oneKoszulPositiveRetractionX_neg_one,
          oneKoszulPositiveRetractionX_zero, Category.assoc]
        rw [oneKoszul_generator_d]
      · rw [← Category.assoc (oneKoszulSquareLeft a)
          ((tensorSquare (oneKoszulComplex a)).d (-1) 0), oneKoszulSquareLeft_d]
        simp [Linear.comp_smul, Linear.smul_comp, smul_smul, Category.assoc,
          htwo]
      · rw [← Category.assoc (oneKoszulSquareRight a)
          ((tensorSquare (oneKoszulComplex a)).d (-1) 0), oneKoszulSquareRight_d]
        simp [Linear.comp_smul, Linear.smul_comp, smul_smul, Category.assoc,
          htwo]
    · by_cases hn0 : n = 0
      · subst n
        exact (oneKoszul_isZero_X_other (2 * a) 1 (by omega)).eq_of_tgt _ _
      · exact (oneKoszulSquare_isZero_X_other a n ⟨hn2, hn, hn0⟩).eq_of_src _ _

def oneKoszulPositiveRetraction (a : R) :
    tensorSquare (oneKoszulComplex a) ⟶ oneKoszulComplex (2 * a) where
  f := oneKoszulPositiveRetractionX a
  comm' n m h := oneKoszulPositiveRetractionX_comm a n m h

lemma oneKoszulPositiveEmbedding_retraction (a : R) :
    oneKoszulPositiveEmbedding a ≫ oneKoszulPositiveRetraction a = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change oneKoszulPositiveEmbeddingX a n ≫ oneKoszulPositiveRetractionX a n = 𝟙 _
  by_cases hn : n = -1
  · subst n
    simp only [oneKoszulPositiveEmbeddingX_neg_one, oneKoszulPositiveRetractionX_neg_one,
      Category.assoc, oneKoszulSquarePositiveGenerator_dual_assoc, Iso.hom_inv_id]
  · by_cases hn0 : n = 0
    · subst n
      simp only [oneKoszulPositiveEmbeddingX_zero, oneKoszulPositiveRetractionX_zero,
        Category.assoc, oneKoszulSquareBottom_dual_assoc, Iso.hom_inv_id]
    · exact (oneKoszul_isZero_X_other (2 * a) n ⟨hn, hn0⟩).eq_of_src _ _

lemma oneKoszulPositiveRetraction_embedding (a : R) :
    oneKoszulPositiveRetraction a ≫ oneKoszulPositiveEmbedding a =
      (tensorSquarePositiveProjector (oneKoszulComplex a)).map := by
  apply HomologicalComplex.Hom.ext
  funext n
  change oneKoszulPositiveRetractionX a n ≫ oneKoszulPositiveEmbeddingX a n = _
  have he : (tensorSquarePositiveProjector (oneKoszulComplex a)).map.f n =
      (⅟(2 : R)) • (𝟙 _ + (tensorSquareSwap (oneKoszulComplex a)).f n) := rfl
  rw [he]
  by_cases hn2 : n = -2
  · subst n
    apply oneKoszulSquareXNegTwo_hom_ext a
    have hz : oneKoszulPositiveRetractionX a (-2) = 0 := by
      simp [oneKoszulPositiveRetractionX]
    rw [hz, zero_comp, comp_zero, Linear.comp_smul, Preadditive.comp_add,
      Category.comp_id, oneKoszulSquareTop_swap, add_neg_cancel, smul_zero]
  · by_cases hn : n = -1
    · subst n
      apply oneKoszulSquareXNegOne_hom_ext a
      all_goals
        simp only [oneKoszulPositiveRetractionX_neg_one, oneKoszulPositiveEmbeddingX_neg_one,
          Category.assoc, Iso.inv_hom_id_assoc, Linear.comp_smul, Preadditive.comp_add,
          Category.comp_id]
      · rw [oneKoszulSquareLeft_positiveDual_assoc, oneKoszulSquareLeft_swap]
        simp [Linear.smul_comp]
      · rw [oneKoszulSquareRight_positiveDual_assoc, oneKoszulSquareRight_swap]
        simp [Linear.smul_comp, add_comm]
    · by_cases hn0 : n = 0
      · subst n
        apply oneKoszulSquareXZero_hom_ext a
        simp only [oneKoszulPositiveRetractionX_zero, oneKoszulPositiveEmbeddingX_zero,
          Category.assoc, Iso.inv_hom_id_assoc, oneKoszulSquareBottom_dual_assoc,
          Linear.comp_smul, Preadditive.comp_add, Category.comp_id, oneKoszulSquareBottom_swap]
        rw [← two_smul R, smul_smul, invOf_mul_self, one_smul]
      · exact (oneKoszulSquare_isZero_X_other a n ⟨hn2, hn, hn0⟩).eq_of_src _ _

def oneKoszulPositiveIso (a : R) :
    oneKoszulComplex (2 * a) ≅ tensorSquarePositive (oneKoszulComplex a) where
  hom := oneKoszulPositiveImageEmbedding a
  inv := (tensorSquarePositiveProjector (oneKoszulComplex a)).inclusion ≫
    oneKoszulPositiveRetraction a
  hom_inv_id := by
    rw [← Category.assoc, oneKoszulPositiveImageEmbedding_inclusion,
      oneKoszulPositiveEmbedding_retraction]
  inv_hom_id := by
    apply (cancel_mono (tensorSquarePositiveProjector (oneKoszulComplex a)).inclusion).mp
    simp only [Category.assoc, oneKoszulPositiveImageEmbedding_inclusion]
    rw [oneKoszulPositiveRetraction_embedding,
      CochainIdempotent.inclusion_map, Category.id_comp]

@[reassoc]
lemma oneKoszulPositiveIso_hom_inclusion (a : R) :
    (oneKoszulPositiveIso a).hom ≫
      (tensorSquarePositiveProjector (oneKoszulComplex a)).inclusion =
      oneKoszulPositiveEmbedding a :=
  oneKoszulPositiveImageEmbedding_inclusion a

lemma oneKoszulPositiveModel_support (a : R) :
    HasHomologySupportOn (oneKoszulSupport a) (oneKoszulComplex (2 * a)) :=
  (tensorSquarePositive_support (oneKoszulComplex_perfect a)
    (oneKoszulComplex_support a)).of_iso (oneKoszulPositiveIso a).symm

end Adams
end SerrePositivity
