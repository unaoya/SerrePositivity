module

public import SerrePositivity.PerfectComplex.Eigen.Idempotent
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import SerrePositivity.PerfectComplex.Eigen.Involution
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.PerfectComplex.ClosedSupportBiproduct

/-! # 二つの対合のテンソルの固有空間

## 概要

二つの対合のテンソル積の四つの固有空間の射影を与え、対合の固有空間の類の差がテンソル積について乗法的であることを示す。

## 方針

四つの射影の直交性と和が 1 であることから、類を和因子ごとに比べる。

## 規約

固有空間の射影は `Eigen/Involution` のもの。

## 使われ方

KTheory/Adams の二乗の作用素の乗法性。
-/

@[expose] public noncomputable section

universe u

section InvolutionTensorPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

end InvolutionTensorPart

section InvolutionTensorClassPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R] [Invertible (2 : R)]
namespace CochainInvolution
variable {P Q : CochainComplex (ModuleCat.{u} R) ℤ}

def positiveClass (t : CochainInvolution P) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) : K0WithSupport Z :=
  t.positive.k0Class Z hp hs

def negativeClass (t : CochainInvolution P) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) : K0WithSupport Z :=
  t.negative.k0Class Z hp hs

lemma positive_tensor_class (t : CochainInvolution P) (s : CochainInvolution Q)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Y P) (hsQ : HasHomologySupportOn Z Q) :
    (t.tensor s).positiveClass (Y ⊓ Z) (strictlyPerfectComplex_cochainTensor P Q hp hq)
      (hsP.cochainTensor hsQ hp hq) =
    K0WithSupport.cup (t.positiveClass Y hp hsP) (s.positiveClass Z hq hsQ) +
      K0WithSupport.cup (t.negativeClass Y hp hsP) (s.negativeClass Z hq hsQ) := by
  let ha := t.positive.image_strictlyPerfect hp
  let hb := s.positive.image_strictlyPerfect hq
  let hc := t.negative.image_strictlyPerfect hp
  let hd := s.negative.image_strictlyPerfect hq
  let sa := t.positive.image_support hsP
  let sb := s.positive.image_support hsQ
  let sc := t.negative.image_support hsP
  let sd := s.negative.image_support hsQ
  let hAB := strictlyPerfectComplex_cochainTensor _ _ ha hb
  let hCD := strictlyPerfectComplex_cochainTensor _ _ hc hd
  let sAB := sa.cochainTensor sb ha hb
  let sCD := sc.cochainTensor sd hc hd
  have he := K0WithSupport.mk_eq_of_quasiIso (Y ⊓ Z)
    (cochainTensor t.positive.image s.positive.image ⊞
      cochainTensor t.negative.image s.negative.image)
    (t.tensor s).positive.image
    (strictlyPerfectComplex_biprod hAB hCD)
    ((t.tensor s).positive.image_strictlyPerfect (strictlyPerfectComplex_cochainTensor P Q hp hq))
    (sAB.biprod sCD) ((t.tensor s).positive.image_support (hsP.cochainTensor hsQ hp hq))
    (positiveTensorIso t s).hom
  have hsum := K0WithSupport.mk_biprod (Y ⊓ Z)
    (cochainTensor t.positive.image s.positive.image)
    (cochainTensor t.negative.image s.negative.image)
    hAB hCD sAB sCD
  have hcups := congrArg₂ (fun x y : K0WithSupport (Y ⊓ Z) => x + y)
    (K0WithSupport.mk_tensor t.positive.image s.positive.image ha hb sa sb)
    (K0WithSupport.mk_tensor t.negative.image s.negative.image hc hd sc sd)
  exact he.symm.trans (hsum.trans hcups)

lemma negative_tensor_class (t : CochainInvolution P) (s : CochainInvolution Q)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Y P) (hsQ : HasHomologySupportOn Z Q) :
    (t.tensor s).negativeClass (Y ⊓ Z) (strictlyPerfectComplex_cochainTensor P Q hp hq)
      (hsP.cochainTensor hsQ hp hq) =
    K0WithSupport.cup (t.positiveClass Y hp hsP) (s.negativeClass Z hq hsQ) +
      K0WithSupport.cup (t.negativeClass Y hp hsP) (s.positiveClass Z hq hsQ) := by
  let ha := t.positive.image_strictlyPerfect hp
  let hb := s.negative.image_strictlyPerfect hq
  let hc := t.negative.image_strictlyPerfect hp
  let hd := s.positive.image_strictlyPerfect hq
  let sa := t.positive.image_support hsP
  let sb := s.negative.image_support hsQ
  let sc := t.negative.image_support hsP
  let sd := s.positive.image_support hsQ
  let hAB := strictlyPerfectComplex_cochainTensor _ _ ha hb
  let hCD := strictlyPerfectComplex_cochainTensor _ _ hc hd
  let sAB := sa.cochainTensor sb ha hb
  let sCD := sc.cochainTensor sd hc hd
  have he := K0WithSupport.mk_eq_of_quasiIso (Y ⊓ Z)
    (cochainTensor t.positive.image s.negative.image ⊞
      cochainTensor t.negative.image s.positive.image)
    (t.tensor s).negative.image
    (strictlyPerfectComplex_biprod hAB hCD)
    ((t.tensor s).negative.image_strictlyPerfect (strictlyPerfectComplex_cochainTensor P Q hp hq))
    (sAB.biprod sCD) ((t.tensor s).negative.image_support (hsP.cochainTensor hsQ hp hq))
    (negativeTensorIso t s).hom
  have hsum := K0WithSupport.mk_biprod (Y ⊓ Z)
    (cochainTensor t.positive.image s.negative.image)
    (cochainTensor t.negative.image s.positive.image)
    hAB hCD sAB sCD
  have hcups := congrArg₂ (fun x y : K0WithSupport (Y ⊓ Z) => x + y)
    (K0WithSupport.mk_tensor t.positive.image s.negative.image ha hb sa sb)
    (K0WithSupport.mk_tensor t.negative.image s.positive.image hc hd sc sd)
  exact he.symm.trans (hsum.trans hcups)

lemma k0Class_tensor (t : CochainInvolution P) (s : CochainInvolution Q)
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Y P) (hsQ : HasHomologySupportOn Z Q) :
    (t.tensor s).k0Class (Y ⊓ Z) (strictlyPerfectComplex_cochainTensor P Q hp hq)
      (hsP.cochainTensor hsQ hp hq) =
    K0WithSupport.cup (t.k0Class Y hp hsP) (s.k0Class Z hq hsQ) := by
  let hT := strictlyPerfectComplex_cochainTensor P Q hp hq
  let sT := hsP.cochainTensor hsQ hp hq
  change (t.tensor s).positiveClass (Y ⊓ Z) hT sT - (t.tensor s).negativeClass (Y ⊓ Z) hT sT =
    K0WithSupport.cup (t.positiveClass Y hp hsP - t.negativeClass Y hp hsP)
      (s.positiveClass Z hq hsQ - s.negativeClass Z hq hsQ)
  rw [positive_tensor_class t s hp hq hsP hsQ, negative_tensor_class t s hp hq hsP hsQ]
  simp only [map_sub, AddMonoidHom.sub_apply]
  abel

end CochainInvolution
end SerrePositivity

end InvolutionTensorClassPart
