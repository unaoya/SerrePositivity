module

public import SerrePositivity.PerfectComplex.IdempotentImagePerfect
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import Mathlib.Algebra.Ring.Invertible

/-! # Positive and negative parts of involutions on complexes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]

/-- A chain involution. -/
structure CochainInvolution (K : CochainComplex (ModuleCat.{u} R) ℤ) where
  map : K ⟶ K
  sq : map ≫ map = 𝟙 K

namespace CochainInvolution
variable {K : CochainComplex (ModuleCat.{u} R) ℤ} [Invertible (2 : R)]

/-- The projector onto the positive eigenspace. -/
def positiveMap (t : CochainInvolution K) : K ⟶ K := (⅟(2 : R)) • (𝟙 K + t.map)

@[simp]
lemma positiveMap_comp_map (t : CochainInvolution K) :
    t.positiveMap ≫ t.map = t.positiveMap := by
  simp [positiveMap, add_comp, t.sq, add_comm]

lemma positiveMap_idem (t : CochainInvolution K) :
    t.positiveMap ≫ t.positiveMap = t.positiveMap := by
  change t.positiveMap ≫ ((⅟(2 : R)) • (𝟙 K + t.map)) = t.positiveMap
  rw [Linear.comp_smul, comp_add, comp_id, positiveMap_comp_map,
    smul_add, ← add_smul, invOf_two_add_invOf_two, one_smul]

/-- The positive projector as an idempotent. -/
def positive (t : CochainInvolution K) : CochainIdempotent K :=
  ⟨t.positiveMap, t.positiveMap_idem⟩

/-- The negative projector, complementary to the positive projector. -/
def negative (t : CochainInvolution K) : CochainIdempotent K := t.positive.complement

lemma negative_map (t : CochainInvolution K) :
    t.negative.map = (⅟(2 : R)) • (𝟙 K - t.map) := by
  have h : (𝟙 K : K ⟶ K) - (⅟(2 : R)) • 𝟙 K = (⅟(2 : R)) • 𝟙 K := by
    calc
      _ = (1 - (⅟(2 : R))) • (𝟙 K : K ⟶ K) := by rw [sub_smul, one_smul]
      _ = _ := by rw [one_sub_invOf_two]
  change 𝟙 K - (⅟(2 : R)) • (𝟙 K + t.map) = _
  rw [smul_add, smul_sub, ← sub_sub, h]

@[simp]
lemma negative_map_comp_map (t : CochainInvolution K) :
    t.negative.map ≫ t.map = -t.negative.map := by
  rw [negative_map, Linear.smul_comp, sub_comp, id_comp, t.sq]
  simp only [smul_sub, neg_sub]

/-- The complex is the direct sum of its positive and negative parts. -/
def decompositionIso (t : CochainInvolution K) : t.positive.image ⊞ t.negative.image ≅ K :=
  t.positive.complementIso

@[reassoc]
lemma positive_inclusion_map (t : CochainInvolution K) :
    t.positive.inclusion ≫ t.map = t.positive.inclusion := by
  rw [← t.positive.inclusion_map, Category.assoc]
  change t.positive.inclusion ≫ (t.positiveMap ≫ t.map) = _
  rw [positiveMap_comp_map]
  rfl

@[reassoc]
lemma negative_inclusion_map (t : CochainInvolution K) :
    t.negative.inclusion ≫ t.map = -t.negative.inclusion := by
  calc
    _ = t.negative.inclusion ≫ (t.negative.map ≫ t.map) := by
      rw [← Category.assoc, t.negative.inclusion_map]
    _ = t.negative.inclusion ≫ (-t.negative.map) := by rw [negative_map_comp_map]
    _ = _ := by rw [comp_neg, t.negative.inclusion_map]

end CochainInvolution
end SerrePositivity
