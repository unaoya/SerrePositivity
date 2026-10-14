module

public import SerrePositivity.KTheory.Adams.KoszulNegativeEmbedding

/-! # The negative Koszul eigenspace is the shifted one-element Koszul complex -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R] [Invertible (2 : R)]
namespace Adams

abbrev oneKoszulSquareNegativeDual (a : R) :=
  (⅟(2 : R)) • (oneKoszulSquareLeftDual a - oneKoszulSquareRightDual a)

@[reassoc (attr := simp)]
lemma oneKoszulSquareLeft_negativeDual (a : R) :
    oneKoszulSquareLeft a ≫ oneKoszulSquareNegativeDual a = (⅟(2 : R)) • 𝟙 _ := by
  simp [oneKoszulSquareNegativeDual, Linear.comp_smul]

@[reassoc (attr := simp)]
lemma oneKoszulSquareRight_negativeDual (a : R) :
    oneKoszulSquareRight a ≫ oneKoszulSquareNegativeDual a = -((⅟(2 : R)) • 𝟙 _) := by
  simp [oneKoszulSquareNegativeDual, Linear.comp_smul]

@[reassoc]
lemma oneKoszulSquareNegativeGenerator_dual (a : R) :
    oneKoszulSquareNegativeGenerator a ≫ oneKoszulSquareNegativeDual a = 𝟙 _ := by
  rw [Preadditive.sub_comp, oneKoszulSquareLeft_negativeDual,
    oneKoszulSquareRight_negativeDual, sub_neg_eq_add, ← two_smul R, smul_smul]
  simp

def oneKoszulNegativeRetractionX (a : R) (n : ℤ) :
    (tensorSquare (oneKoszulComplex a)).X n ⟶ (oneKoszulShiftOne a).X n :=
  if h : n = -2 then
    ((tensorSquare (oneKoszulComplex a)).XIsoOfEq h).hom ≫ oneKoszulSquareTopDual a ≫
      (oneKoszulShiftOneXNegTwoIso a).inv ≫ ((oneKoszulShiftOne a).XIsoOfEq h).inv
  else if h : n = -1 then
    ((tensorSquare (oneKoszulComplex a)).XIsoOfEq h).hom ≫ oneKoszulSquareNegativeDual a ≫
      (oneKoszulShiftOneXNegOneIso a).inv ≫ ((oneKoszulShiftOne a).XIsoOfEq h).inv
  else 0

@[simp]
lemma oneKoszulNegativeRetractionX_neg_two (a : R) :
    oneKoszulNegativeRetractionX a (-2) =
      oneKoszulSquareTopDual a ≫ (oneKoszulShiftOneXNegTwoIso a).inv := by
  simp [oneKoszulNegativeRetractionX]

@[simp]
lemma oneKoszulNegativeRetractionX_neg_one (a : R) :
    oneKoszulNegativeRetractionX a (-1) =
      oneKoszulSquareNegativeDual a ≫ (oneKoszulShiftOneXNegOneIso a).inv := by
  simp [oneKoszulNegativeRetractionX]

lemma oneKoszulNegativeRetractionX_comm (a : R) (n m : ℤ) (h : n + 1 = m) :
    oneKoszulNegativeRetractionX a n ≫ (oneKoszulShiftOne a).d n m =
      (tensorSquare (oneKoszulComplex a)).d n m ≫ oneKoszulNegativeRetractionX a m := by
  subst m
  by_cases hn2 : n = -2
  · subst n
    apply oneKoszulSquareXNegTwo_hom_ext a
    simp only [Int.reduceNeg, Int.reduceAdd, oneKoszulNegativeRetractionX_neg_two,
      oneKoszulNegativeRetractionX_neg_one, Category.assoc, oneKoszulSquareTop_dual_assoc]
    rw [oneKoszulShiftOne_generator_d,
      ← Category.assoc (oneKoszulSquareTop a) ((tensorSquare (oneKoszulComplex a)).d (-2) (-1)),
      oneKoszulSquareTop_d_negative]
    rw [Preadditive.neg_comp, Linear.smul_comp,
      oneKoszulSquareNegativeGenerator_dual_assoc]
  · by_cases hn1 : n = -1
    · subst n
      exact (oneKoszulShiftOne_isZero_X_other a 0 (by omega)).eq_of_tgt _ _
    · by_cases hn0 : n = 0
      · subst n
        exact (oneKoszulShiftOne_isZero_X_other a 1 (by omega)).eq_of_tgt _ _
      · exact (oneKoszulSquare_isZero_X_other a n ⟨hn2, hn1, hn0⟩).eq_of_src _ _

def oneKoszulNegativeRetraction (a : R) :
    tensorSquare (oneKoszulComplex a) ⟶ oneKoszulShiftOne a where
  f := oneKoszulNegativeRetractionX a
  comm' n m h := oneKoszulNegativeRetractionX_comm a n m h

lemma oneKoszulNegativeEmbedding_retraction (a : R) :
    oneKoszulNegativeEmbedding a ≫ oneKoszulNegativeRetraction a = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change oneKoszulNegativeEmbeddingX a n ≫ oneKoszulNegativeRetractionX a n = 𝟙 _
  by_cases hn2 : n = -2
  · subst n
    simp only [oneKoszulNegativeEmbeddingX_neg_two, oneKoszulNegativeRetractionX_neg_two,
      Category.assoc, oneKoszulSquareTop_dual_assoc, Iso.hom_inv_id]
  · by_cases hn1 : n = -1
    · subst n
      simp only [oneKoszulNegativeEmbeddingX_neg_one, oneKoszulNegativeRetractionX_neg_one,
        Category.assoc, oneKoszulSquareNegativeGenerator_dual_assoc, Iso.hom_inv_id]
    · exact (oneKoszulShiftOne_isZero_X_other a n ⟨hn2, hn1⟩).eq_of_src _ _

lemma oneKoszulNegativeRetraction_embedding (a : R) :
    oneKoszulNegativeRetraction a ≫ oneKoszulNegativeEmbedding a =
      (tensorSquareNegativeProjector (oneKoszulComplex a)).map := by
  apply HomologicalComplex.Hom.ext
  funext n
  change oneKoszulNegativeRetractionX a n ≫ oneKoszulNegativeEmbeddingX a n = _
  have he : (tensorSquareNegativeProjector (oneKoszulComplex a)).map.f n =
      (⅟(2 : R)) • (𝟙 _ - (tensorSquareSwap (oneKoszulComplex a)).f n) :=
    congrArg (fun f => f.f n) (tensorSquareNegativeProjector_map (oneKoszulComplex a))
  rw [he]
  by_cases hn2 : n = -2
  · subst n
    apply oneKoszulSquareXNegTwo_hom_ext a
    simp only [oneKoszulNegativeRetractionX_neg_two, oneKoszulNegativeEmbeddingX_neg_two,
      Category.assoc, Iso.inv_hom_id_assoc, oneKoszulSquareTop_dual_assoc,
      Linear.comp_smul, Preadditive.comp_sub, Category.comp_id, oneKoszulSquareTop_swap]
    rw [sub_neg_eq_add, ← two_smul R, smul_smul, invOf_mul_self, one_smul]
  · by_cases hn1 : n = -1
    · subst n
      apply oneKoszulSquareXNegOne_hom_ext a
      all_goals
        simp only [oneKoszulNegativeRetractionX_neg_one, oneKoszulNegativeEmbeddingX_neg_one,
          Category.assoc, Iso.inv_hom_id_assoc, Linear.comp_smul, Preadditive.comp_sub,
          Category.comp_id]
      · rw [oneKoszulSquareLeft_negativeDual_assoc, oneKoszulSquareLeft_swap]
        simp [Linear.smul_comp, smul_sub]
      · rw [oneKoszulSquareRight_negativeDual_assoc, oneKoszulSquareRight_swap]
        simp [Linear.smul_comp, smul_sub, sub_eq_add_neg, add_comm]
    · by_cases hn0 : n = 0
      · subst n
        apply oneKoszulSquareXZero_hom_ext a
        have hz : oneKoszulNegativeRetractionX a 0 = 0 := by
          simp [oneKoszulNegativeRetractionX]
        rw [hz, zero_comp, comp_zero, Linear.comp_smul, Preadditive.comp_sub,
          Category.comp_id, oneKoszulSquareBottom_swap, sub_self, smul_zero]
      · exact (oneKoszulSquare_isZero_X_other a n ⟨hn2, hn1, hn0⟩).eq_of_src _ _

def oneKoszulNegativeIso (a : R) :
    oneKoszulShiftOne a ≅ tensorSquareNegative (oneKoszulComplex a) where
  hom := oneKoszulNegativeImageEmbedding a
  inv := (tensorSquareNegativeProjector (oneKoszulComplex a)).inclusion ≫
    oneKoszulNegativeRetraction a
  hom_inv_id := by
    rw [← Category.assoc, oneKoszulNegativeImageEmbedding_inclusion,
      oneKoszulNegativeEmbedding_retraction]
  inv_hom_id := by
    apply (cancel_mono (tensorSquareNegativeProjector (oneKoszulComplex a)).inclusion).mp
    simp only [Category.assoc, oneKoszulNegativeImageEmbedding_inclusion]
    rw [oneKoszulNegativeRetraction_embedding,
      CochainIdempotent.inclusion_map, Category.id_comp]

@[reassoc]
lemma oneKoszulNegativeIso_hom_inclusion (a : R) :
    (oneKoszulNegativeIso a).hom ≫
      (tensorSquareNegativeProjector (oneKoszulComplex a)).inclusion =
      oneKoszulNegativeEmbedding a :=
  oneKoszulNegativeImageEmbedding_inclusion a

omit [Invertible (2 : R)] in
lemma oneKoszulNegativeModel_support (a : R) :
    HasHomologySupportOn (oneKoszulSupport a) (oneKoszulShiftOne a) :=
  (oneKoszulComplex_support a).shift 1

end Adams
end SerrePositivity
