module

public import SerrePositivity.KTheory.Adams.KoszulSquare
public import SerrePositivity.KTheory.Adams.TensorPower.TensorSquare

/-! # Koszul のテンソル二乗の正と負の和因子

## 概要

テンソル二乗の中の正の Koszul 和因子への埋め込みと鎖の引き込み、双対座標、一段シフトした一元 Koszul モデル、負の固有空間がシフトした一元 Koszul 複体であることを与える。

## 方針

埋め込みと引き込みを座標で明示し、合成が恒等であることを確かめる。

## 規約

正と負の版は並行していて、ε で一本化できる（refactor-plan §6.3）。

## 使われ方

`Adams/CyclicTwo` の Koszul の正規化。
-/

@[expose] public noncomputable section

universe u

section KoszulPositiveEmbeddingPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

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

end KoszulPositiveEmbeddingPart

section KoszulSquareDualPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]
namespace Adams

abbrev oneKoszulSquareBottomDual (a : R) :=
  (oneKoszulSquareConeIso a).hom.f 0 ≫
    (mappingCone.snd (smulId a (oneKoszulComplex a))).v 0 0 (by omega) ≫
    (oneKoszulXZeroIso a).hom

abbrev oneKoszulSquareLeftDual (a : R) :=
  (oneKoszulSquareConeIso a).hom.f (-1) ≫
    (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v (-1) 0 (by omega) ≫
    (oneKoszulXZeroIso a).hom

abbrev oneKoszulSquareRightDual (a : R) :=
  (oneKoszulSquareConeIso a).hom.f (-1) ≫
    (mappingCone.snd (smulId a (oneKoszulComplex a))).v (-1) (-1) (by omega) ≫
    (oneKoszulXNegOneIso a).hom

abbrev oneKoszulSquareTopDual (a : R) :=
  (oneKoszulSquareConeIso a).hom.f (-2) ≫
    (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v (-2) (-1) (by omega) ≫
    (oneKoszulXNegOneIso a).hom

@[reassoc (attr := simp)]
lemma oneKoszulSquareBottom_dual (a : R) :
    oneKoszulSquareBottom a ≫ oneKoszulSquareBottomDual a = 𝟙 _ := by
  rw [oneKoszulSquareBottom_cone_assoc]
  simp

@[reassoc (attr := simp)]
lemma oneKoszulSquareLeft_dual (a : R) :
    oneKoszulSquareLeft a ≫ oneKoszulSquareLeftDual a = 𝟙 _ := by
  rw [oneKoszulSquareLeft_cone_assoc]
  simp

@[reassoc (attr := simp)]
lemma oneKoszulSquareLeft_rightDual (a : R) :
    oneKoszulSquareLeft a ≫ oneKoszulSquareRightDual a = 0 := by
  rw [oneKoszulSquareLeft_cone_assoc]
  simp

@[reassoc (attr := simp)]
lemma oneKoszulSquareRight_leftDual (a : R) :
    oneKoszulSquareRight a ≫ oneKoszulSquareLeftDual a = 0 := by
  rw [oneKoszulSquareRight_cone_assoc]
  simp

@[reassoc (attr := simp)]
lemma oneKoszulSquareRight_dual (a : R) :
    oneKoszulSquareRight a ≫ oneKoszulSquareRightDual a = 𝟙 _ := by
  rw [oneKoszulSquareRight_cone_assoc]
  simp

@[reassoc (attr := simp)]
lemma oneKoszulSquareTop_dual (a : R) :
    oneKoszulSquareTop a ≫ oneKoszulSquareTopDual a = 𝟙 _ := by
  rw [oneKoszulSquareTop_cone_assoc]
  simp

end Adams
end SerrePositivity

end KoszulSquareDualPart

section KoszulPositiveRetractionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

end KoszulPositiveRetractionPart

section KoszulShiftOneModelPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]
namespace Adams

abbrev oneKoszulShiftOne (a : R) := (oneKoszulComplex a)⟦(1 : ℤ)⟧

def oneKoszulShiftOneXNegOneIso (a : R) :
    (oneKoszulShiftOne a).X (-1) ≅ ModuleCat.of R R :=
  (oneKoszulComplex a).shiftFunctorObjXIso 1 (-1) 0 (by omega) ≪≫ oneKoszulXZeroIso a

def oneKoszulShiftOneXNegTwoIso (a : R) :
    (oneKoszulShiftOne a).X (-2) ≅ ModuleCat.of R R :=
  (oneKoszulComplex a).shiftFunctorObjXIso 1 (-2) (-1) (by omega) ≪≫ oneKoszulXNegOneIso a

lemma oneKoszulShiftOne_isZero_X_other (a : R) (n : ℤ) (hn : n ≠ -2 ∧ n ≠ -1) :
    IsZero ((oneKoszulShiftOne a).X n) :=
  (oneKoszul_isZero_X_other a (n + 1) (by omega)).of_iso
    ((oneKoszulComplex a).shiftFunctorObjXIso 1 n (n + 1) rfl)

lemma oneKoszulShiftOne_generator_d (a : R) :
    (oneKoszulShiftOneXNegTwoIso a).inv ≫ (oneKoszulShiftOne a).d (-2) (-1) =
      -(a • (oneKoszulShiftOneXNegOneIso a).inv) := by
  change (oneKoszulXNegOneIso a).inv ≫
    ((1 : ℤ).negOnePow • (oneKoszulComplex a).d (-1) 0) = _
  simp only [Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.comp_neg]
  rw [oneKoszul_generator_d]
  rfl

abbrev oneKoszulSquareNegativeGenerator (a : R) :=
  oneKoszulSquareLeft a - oneKoszulSquareRight a

lemma oneKoszulSquareNegativeGenerator_d (a : R) :
    oneKoszulSquareNegativeGenerator a ≫ (tensorSquare (oneKoszulComplex a)).d (-1) 0 = 0 := by
  rw [Preadditive.sub_comp, oneKoszulSquareLeft_d, oneKoszulSquareRight_d, sub_self]

lemma oneKoszulSquareTop_d_negative (a : R) :
    oneKoszulSquareTop a ≫ (tensorSquare (oneKoszulComplex a)).d (-2) (-1) =
      -(a • oneKoszulSquareNegativeGenerator a) := by
  rw [oneKoszulSquareTop_d]
  simp [oneKoszulSquareNegativeGenerator, smul_sub, neg_sub]

end Adams
end SerrePositivity

end KoszulShiftOneModelPart

section KoszulNegativeEmbeddingPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

end KoszulNegativeEmbeddingPart

section KoszulNegativeRetractionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

end KoszulNegativeRetractionPart
