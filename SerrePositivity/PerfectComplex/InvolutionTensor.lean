module

public import SerrePositivity.PerfectComplex.IdempotentTensor
public import SerrePositivity.PerfectComplex.IdempotentImagePerfect
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import SerrePositivity.PerfectComplex.InvolutionMaps
public import SerrePositivity.HomologicalAlgebra.CochainTensorLinear

/-! # The four tensor eigenspace projectors of two involutions -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

namespace CochainInvolution
variable {P Q : CochainComplex (ModuleCat.{u} R) ℤ}

def tensor (t : CochainInvolution P) (s : CochainInvolution Q) :
    CochainInvolution (cochainTensor P Q) where
  map := cochainTensorMap t.map s.map
  sq := by rw [cochainTensorMap_comp, t.sq, s.sq, cochainTensorMap_id]

variable [Invertible (2 : R)]

abbrev positivePositive (t : CochainInvolution P) (s : CochainInvolution Q) :=
  CochainIdempotent.tensor t.positive s.positive
abbrev negativeNegative (t : CochainInvolution P) (s : CochainInvolution Q) :=
  CochainIdempotent.tensor t.negative s.negative
abbrev positiveNegative (t : CochainInvolution P) (s : CochainInvolution Q) :=
  CochainIdempotent.tensor t.positive s.negative
abbrev negativePositive (t : CochainInvolution P) (s : CochainInvolution Q) :=
  CochainIdempotent.tensor t.negative s.positive

lemma positive_tensor_map (t : CochainInvolution P) (s : CochainInvolution Q) :
    (t.tensor s).positive.map = (positivePositive t s).map + (negativeNegative t s).map := by
  have hinv : (⅟(2 : R) * ⅟(2 : R)) * 2 = ⅟(2 : R) := by
    rw [mul_assoc, invOf_mul_self, mul_one]
  change (⅟(2 : R)) • (𝟙 _ + cochainTensorMap t.map s.map) = _
  change _ = cochainTensorMap t.positive.map s.positive.map +
    cochainTensorMap t.negative.map s.negative.map
  rw [negative_map, negative_map]
  change _ = cochainTensorMap ((⅟(2 : R)) • (𝟙 P + t.map))
      ((⅟(2 : R)) • (𝟙 Q + s.map)) +
    cochainTensorMap ((⅟(2 : R)) • (𝟙 P - t.map)) ((⅟(2 : R)) • (𝟙 Q - s.map))
  rw [cochainTensorMap_smul_left, cochainTensorMap_smul_right,
    cochainTensorMap_smul_left, cochainTensorMap_smul_right, smul_smul, smul_smul,
    cochainTensorMap_add_left, cochainTensorMap_add_right, cochainTensorMap_add_right,
    cochainTensorMap_sub_left, cochainTensorMap_sub_right, cochainTensorMap_sub_right,
    cochainTensorMap_id, ← smul_add]
  have he : (𝟙 (cochainTensor P Q) + cochainTensorMap (𝟙 P) s.map +
      (cochainTensorMap t.map (𝟙 Q) + cochainTensorMap t.map s.map)) +
      ((𝟙 (cochainTensor P Q) - cochainTensorMap (𝟙 P) s.map) -
        (cochainTensorMap t.map (𝟙 Q) - cochainTensorMap t.map s.map)) =
      (𝟙 _ + cochainTensorMap t.map s.map) + (𝟙 _ + cochainTensorMap t.map s.map) := by abel
  rw [he, ← two_smul R, smul_smul, hinv]

lemma negative_tensor_map (t : CochainInvolution P) (s : CochainInvolution Q) :
    (t.tensor s).negative.map = (positiveNegative t s).map + (negativePositive t s).map := by
  have hinv : (⅟(2 : R) * ⅟(2 : R)) * 2 = ⅟(2 : R) := by
    rw [mul_assoc, invOf_mul_self, mul_one]
  rw [negative_map]
  change (⅟(2 : R)) • (𝟙 _ - cochainTensorMap t.map s.map) = _
  change _ = cochainTensorMap t.positive.map s.negative.map +
    cochainTensorMap t.negative.map s.positive.map
  rw [negative_map, negative_map]
  change _ = cochainTensorMap ((⅟(2 : R)) • (𝟙 P + t.map))
      ((⅟(2 : R)) • (𝟙 Q - s.map)) +
    cochainTensorMap ((⅟(2 : R)) • (𝟙 P - t.map)) ((⅟(2 : R)) • (𝟙 Q + s.map))
  rw [cochainTensorMap_smul_left, cochainTensorMap_smul_right,
    cochainTensorMap_smul_left, cochainTensorMap_smul_right, smul_smul, smul_smul,
    cochainTensorMap_add_left, cochainTensorMap_sub_right, cochainTensorMap_sub_right,
    cochainTensorMap_sub_left, cochainTensorMap_add_right, cochainTensorMap_add_right,
    cochainTensorMap_id, ← smul_add]
  have he : (𝟙 (cochainTensor P Q) - cochainTensorMap (𝟙 P) s.map +
      (cochainTensorMap t.map (𝟙 Q) - cochainTensorMap t.map s.map)) +
      ((𝟙 (cochainTensor P Q) + cochainTensorMap (𝟙 P) s.map) -
        (cochainTensorMap t.map (𝟙 Q) + cochainTensorMap t.map s.map)) =
      (𝟙 _ - cochainTensorMap t.map s.map) + (𝟙 _ - cochainTensorMap t.map s.map) := by abel
  rw [he, ← two_smul R, smul_smul, hinv]

lemma positivePositive_comp_negativeNegative (t : CochainInvolution P) (s : CochainInvolution Q) :
    (positivePositive t s).map ≫ (negativeNegative t s).map = 0 := by
  change cochainTensorMap t.positive.map s.positive.map ≫
    cochainTensorMap t.negative.map s.negative.map = _
  rw [cochainTensorMap_comp]
  have hz : t.positive.map ≫ t.negative.map = 0 :=
    CochainIdempotent.map_comp_complement t.positive
  rw [hz, cochainTensorMap_zero_left]

lemma negativeNegative_comp_positivePositive (t : CochainInvolution P) (s : CochainInvolution Q) :
    (negativeNegative t s).map ≫ (positivePositive t s).map = 0 := by
  change cochainTensorMap t.negative.map s.negative.map ≫
    cochainTensorMap t.positive.map s.positive.map = _
  rw [cochainTensorMap_comp]
  have hz : t.negative.map ≫ t.positive.map = 0 :=
    CochainIdempotent.complement_comp_map t.positive
  rw [hz, cochainTensorMap_zero_left]

lemma positiveNegative_comp_negativePositive (t : CochainInvolution P) (s : CochainInvolution Q) :
    (positiveNegative t s).map ≫ (negativePositive t s).map = 0 := by
  change cochainTensorMap t.positive.map s.negative.map ≫
    cochainTensorMap t.negative.map s.positive.map = _
  rw [cochainTensorMap_comp]
  have hz : t.positive.map ≫ t.negative.map = 0 :=
    CochainIdempotent.map_comp_complement t.positive
  rw [hz, cochainTensorMap_zero_left]

lemma negativePositive_comp_positiveNegative (t : CochainInvolution P) (s : CochainInvolution Q) :
    (negativePositive t s).map ≫ (positiveNegative t s).map = 0 := by
  change cochainTensorMap t.negative.map s.positive.map ≫
    cochainTensorMap t.positive.map s.negative.map = _
  rw [cochainTensorMap_comp]
  have hz : t.negative.map ≫ t.positive.map = 0 :=
    CochainIdempotent.complement_comp_map t.positive
  rw [hz, cochainTensorMap_zero_left]

lemma positive_tensor_sum_eq (t : CochainInvolution P) (s : CochainInvolution Q) :
    CochainIdempotent.orthogonalSum (positivePositive t s) (negativeNegative t s)
      (positivePositive_comp_negativeNegative t s) (negativeNegative_comp_positivePositive t s) =
    (t.tensor s).positive :=
  CochainIdempotent.ext (positive_tensor_map t s).symm

lemma negative_tensor_sum_eq (t : CochainInvolution P) (s : CochainInvolution Q) :
    CochainIdempotent.orthogonalSum (positiveNegative t s) (negativePositive t s)
      (positiveNegative_comp_negativePositive t s) (negativePositive_comp_positiveNegative t s) =
    (t.tensor s).negative :=
  CochainIdempotent.ext (negative_tensor_map t s).symm

def positiveTensorIso (t : CochainInvolution P) (s : CochainInvolution Q) :
    cochainTensor t.positive.image s.positive.image ⊞
      cochainTensor t.negative.image s.negative.image ≅ (t.tensor s).positive.image :=
  biprod.mapIso (CochainIdempotent.imageTensorIso t.positive s.positive)
      (CochainIdempotent.imageTensorIso t.negative s.negative) ≪≫
    CochainIdempotent.imageOrthogonalSumIso _ _
      (positivePositive_comp_negativeNegative t s) (negativeNegative_comp_positivePositive t s) ≪≫
    eqToIso (congrArg CochainIdempotent.image (positive_tensor_sum_eq t s))

def negativeTensorIso (t : CochainInvolution P) (s : CochainInvolution Q) :
    cochainTensor t.positive.image s.negative.image ⊞
      cochainTensor t.negative.image s.positive.image ≅ (t.tensor s).negative.image :=
  biprod.mapIso (CochainIdempotent.imageTensorIso t.positive s.negative)
      (CochainIdempotent.imageTensorIso t.negative s.positive) ≪≫
    CochainIdempotent.imageOrthogonalSumIso _ _
      (positiveNegative_comp_negativePositive t s) (negativePositive_comp_positiveNegative t s) ≪≫
    eqToIso (congrArg CochainIdempotent.image (negative_tensor_sum_eq t s))

@[reassoc]
lemma positiveTensorIso_hom_inclusion (t : CochainInvolution P) (s : CochainInvolution Q) :
    (positiveTensorIso t s).hom ≫ (t.tensor s).positive.inclusion =
    biprod.desc (cochainTensorMap t.positive.inclusion s.positive.inclusion)
      (cochainTensorMap t.negative.inclusion s.negative.inclusion) := by
  rw [positiveTensorIso, Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
    CochainIdempotent.image_eqToIso_inclusion (positive_tensor_sum_eq t s),
    CochainIdempotent.imageOrthogonalSumIso_hom_inclusion]
  apply biprod.hom_ext'
  · simp [CochainIdempotent.imageTensorIso_hom_inclusion]
  · simp [CochainIdempotent.imageTensorIso_hom_inclusion]

@[reassoc]
lemma negativeTensorIso_hom_inclusion (t : CochainInvolution P) (s : CochainInvolution Q) :
    (negativeTensorIso t s).hom ≫ (t.tensor s).negative.inclusion =
    biprod.desc (cochainTensorMap t.positive.inclusion s.negative.inclusion)
      (cochainTensorMap t.negative.inclusion s.positive.inclusion) := by
  rw [negativeTensorIso, Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
    CochainIdempotent.image_eqToIso_inclusion (negative_tensor_sum_eq t s),
    CochainIdempotent.imageOrthogonalSumIso_hom_inclusion]
  apply biprod.hom_ext'
  · simp [CochainIdempotent.imageTensorIso_hom_inclusion]
  · simp [CochainIdempotent.imageTensorIso_hom_inclusion]

end CochainInvolution
end SerrePositivity
