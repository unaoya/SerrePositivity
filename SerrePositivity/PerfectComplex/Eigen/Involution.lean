module

public import SerrePositivity.PerfectComplex.Eigen.Idempotent
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.HomologicalAlgebra.BaseChange

/-! # 対合の固有空間

## 概要

複体の対合（位数 2 の鎖作用）の正と負の部分、同変な写像の固有空間への制限、反可換な対合が正と負の固有空間を入れ替えること、係数変更、固有空間の類の差とその非輪状な場合の消滅、同変な短完全列での加法性を与える。

## 方針

2 が可逆な係数で (1 ± τ)/2 を冪等な射影として使う。

## 規約

`map_invOf_two`・`map_invOf_three` は `map_invOf` と `map_ofNat` から一般形 1 本にできる（確度高、refactor-plan §4.4.2）。

## 使われ方

KTheory/Adams の二乗の Adams 作用素。
-/

@[expose] public noncomputable section

universe u

section InvolutionDecompositionPart

set_option backward.isDefEq.respectTransparency false

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

end InvolutionDecompositionPart

section InvolutionMapsPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace CochainInvolution
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

lemma positive_naturality (t : CochainInvolution K) (s : CochainInvolution L)
    (f : K ⟶ L) (hf : t.map ≫ f = f ≫ s.map) :
    t.positive.map ≫ f = f ≫ s.positive.map := by
  change ((⅟(2 : R)) • (𝟙 K + t.map)) ≫ f = f ≫ ((⅟(2 : R)) • (𝟙 L + s.map))
  simp [add_comp, comp_add, hf]

lemma negative_naturality (t : CochainInvolution K) (s : CochainInvolution L)
    (f : K ⟶ L) (hf : t.map ≫ f = f ≫ s.map) :
    t.negative.map ≫ f = f ≫ s.negative.map := by
  change (𝟙 K - t.positive.map) ≫ f = f ≫ (𝟙 L - s.positive.map)
  rw [sub_comp, comp_sub, id_comp, comp_id, positive_naturality t s f hf]

abbrev positiveImageMap (t : CochainInvolution K) (s : CochainInvolution L)
    (f : K ⟶ L) (hf : t.map ≫ f = f ≫ s.map) : t.positive.image ⟶ s.positive.image :=
  CochainIdempotent.imageMap t.positive s.positive f (positive_naturality t s f hf)

abbrev negativeImageMap (t : CochainInvolution K) (s : CochainInvolution L)
    (f : K ⟶ L) (hf : t.map ≫ f = f ≫ s.map) : t.negative.image ⟶ s.negative.image :=
  CochainIdempotent.imageMap t.negative s.negative f (negative_naturality t s f hf)

lemma positiveImageMap_quasiIso (t : CochainInvolution K) (s : CochainInvolution L)
    (f : K ⟶ L) (hf : t.map ≫ f = f ≫ s.map) [QuasiIso f] :
    QuasiIso (positiveImageMap t s f hf) :=
  CochainIdempotent.imageMap_quasiIso _ _ _ _

lemma negativeImageMap_quasiIso (t : CochainInvolution K) (s : CochainInvolution L)
    (f : K ⟶ L) (hf : t.map ≫ f = f ≫ s.map) [QuasiIso f] :
    QuasiIso (negativeImageMap t s f hf) :=
  CochainIdempotent.imageMap_quasiIso _ _ _ _

end CochainInvolution
end SerrePositivity

end InvolutionMapsPart

section InvolutionAntiEquivariancePart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace CochainInvolution
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

lemma positive_negative_comm (t : CochainInvolution K) (a : K ⟶ K)
    (ha : t.map ≫ a = -(a ≫ t.map)) : t.positive.map ≫ a = a ≫ t.negative.map := by
  rw [t.negative_map]
  change ((⅟(2 : R)) • (𝟙 K + t.map)) ≫ a = a ≫ ((⅟(2 : R)) • (𝟙 K - t.map))
  rw [Linear.smul_comp, Linear.comp_smul, add_comp, comp_sub, id_comp, comp_id, ha]
  rw [sub_eq_add_neg]

lemma negative_positive_comm (t : CochainInvolution K) (a : K ⟶ K)
    (ha : t.map ≫ a = -(a ≫ t.map)) : t.negative.map ≫ a = a ≫ t.positive.map := by
  have h := positive_negative_comm t a ha
  change t.positive.map ≫ a = a ≫ (𝟙 K - t.positive.map) at h
  change (𝟙 K - t.positive.map) ≫ a = a ≫ t.positive.map
  rw [comp_sub, comp_id] at h
  rw [sub_comp, id_comp, h]
  abel

/-- An anticommuting chain involution gives a canonical isomorphism of the two eigenspaces. -/
def positiveNegativeIso (t : CochainInvolution K) (a : K ⟶ K)
    (ha : t.map ≫ a = -(a ≫ t.map)) (haa : a ≫ a = 𝟙 K) :
    t.positive.image ≅ t.negative.image where
  hom := CochainIdempotent.imageMap t.positive t.negative a (positive_negative_comm t a ha)
  inv := CochainIdempotent.imageMap t.negative t.positive a (negative_positive_comm t a ha)
  hom_inv_id := by
    apply (cancel_mono t.positive.inclusion).1
    simp only [Category.assoc, CochainIdempotent.imageMap_inclusion,
      CochainIdempotent.imageMap_inclusion_assoc, haa, comp_id, id_comp]
  inv_hom_id := by
    apply (cancel_mono t.negative.inclusion).1
    simp only [Category.assoc, CochainIdempotent.imageMap_inclusion,
      CochainIdempotent.imageMap_inclusion_assoc, haa, comp_id, id_comp]

end CochainInvolution
end SerrePositivity

end InvolutionAntiEquivariancePart

section InvolutionBaseChangePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R S : Type u} [CommRing R] [CommRing S]
namespace CochainInvolution
variable (φ : R →+* S) {K : CochainComplex (ModuleCat.{u} R) ℤ}

def baseChange (t : CochainInvolution K) :
    CochainInvolution (SerrePositivity.baseChange φ K) where
  map := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map t.map
  sq := by rw [← Functor.map_comp, t.sq, CategoryTheory.Functor.map_id]

variable [Invertible (2 : R)] [Invertible (2 : S)]

lemma map_invOf_two : φ (⅟(2 : R)) = ⅟(2 : S) := by
  let : Invertible (φ (2 : R)) := by rw [map_ofNat]; infer_instance
  simpa only [map_ofNat] using map_invOf φ (2 : R)

lemma baseChange_positive_map (t : CochainInvolution K) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map t.positive.map =
      (baseChange φ t).positive.map := by
  change ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
      ((⅟(2 : R)) • (𝟙 K + t.map)) = _
  rw [extendScalars_mapHomologicalComplex_smul, map_invOf_two,
    Functor.map_add, CategoryTheory.Functor.map_id]
  rfl

lemma baseChange_negative_map (t : CochainInvolution K) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map t.negative.map =
      (baseChange φ t).negative.map := by
  change ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
      (𝟙 K - t.positive.map) = _
  rw [Functor.map_sub, CategoryTheory.Functor.map_id, baseChange_positive_map]
  rfl

def positiveBaseChangeIso (t : CochainInvolution K) :
    SerrePositivity.baseChange φ t.positive.image ≅ (baseChange φ t).positive.image :=
  CochainIdempotent.imageFunctorIsoOfMapEq
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)) t.positive
    (baseChange φ t).positive (baseChange_positive_map φ t)

def negativeBaseChangeIso (t : CochainInvolution K) :
    SerrePositivity.baseChange φ t.negative.image ≅ (baseChange φ t).negative.image :=
  CochainIdempotent.imageFunctorIsoOfMapEq
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)) t.negative
    (baseChange φ t).negative (baseChange_negative_map φ t)

@[reassoc]
lemma positiveBaseChangeIso_hom_inclusion (t : CochainInvolution K) :
    (positiveBaseChangeIso φ t).hom ≫ (baseChange φ t).positive.inclusion =
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map t.positive.inclusion := by
  simp only [positiveBaseChangeIso, CochainIdempotent.imageFunctorIsoOfMapEq_hom_inclusion]

@[reassoc]
lemma negativeBaseChangeIso_hom_inclusion (t : CochainInvolution K) :
    (negativeBaseChangeIso φ t).hom ≫ (baseChange φ t).negative.inclusion =
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map t.negative.inclusion := by
  simp only [negativeBaseChangeIso, CochainIdempotent.imageFunctorIsoOfMapEq_hom_inclusion]

end CochainInvolution
end SerrePositivity

end InvolutionBaseChangePart

section InvolutionClassPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace CochainInvolution
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

def k0Class (t : CochainInvolution K) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) : K0WithSupport Z :=
  t.positive.k0Class Z hp hs - t.negative.k0Class Z hp hs

lemma k0Class_eq_zero_of_anticommute (t : CochainInvolution K)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K)
    (a : K ⟶ K) (ha : t.map ≫ a = -(a ≫ t.map)) (haa : a ≫ a = 𝟙 K) :
    t.k0Class Z hp hs = 0 := by
  apply sub_eq_zero.mpr
  let e := t.positiveNegativeIso a ha haa
  exact K0WithSupport.mk_eq_of_quasiIso Z t.positive.image t.negative.image
    (t.positive.image_strictlyPerfect hp) (t.negative.image_strictlyPerfect hp)
    (t.positive.image_support hs) (t.negative.image_support hs) e.hom

end CochainInvolution
end SerrePositivity

end InvolutionClassPart

section InvolutionClassAcyclicPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace CochainInvolution

lemma k0Class_eq_zero_of_acyclic {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (t : CochainInvolution K) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) (hac : K.Acyclic) :
    t.k0Class Z hp hs = 0 := by
  rw [k0Class, t.positive.k0Class_eq_zero_of_acyclic Z hp hs hac,
    t.negative.k0Class_eq_zero_of_acyclic Z hp hs hac, sub_self]

end CochainInvolution

end SerrePositivity

end InvolutionClassAcyclicPart

section InvolutionClassShortExactPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace CochainInvolution

lemma k0Class_shortExact
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (t₁ : CochainInvolution S.X₁) (t₂ : CochainInvolution S.X₂) (t₃ : CochainInvolution S.X₃)
    (hf : t₁.map ≫ S.f = S.f ≫ t₂.map) (hg : t₂.map ≫ S.g = S.g ≫ t₃.map)
    (hS : S.ShortExact)
    (hp₁ : strictlyPerfectComplex R S.X₁) (hp₂ : strictlyPerfectComplex R S.X₂)
    (hp₃ : strictlyPerfectComplex R S.X₃)
    (hs₁ : HasHomologySupportOn Z S.X₁) (hs₂ : HasHomologySupportOn Z S.X₂)
    (hs₃ : HasHomologySupportOn Z S.X₃) :
    t₂.k0Class Z hp₂ hs₂ = t₁.k0Class Z hp₁ hs₁ + t₃.k0Class Z hp₃ hs₃ := by
  have hpos := CochainIdempotent.k0Class_shortExact S t₁.positive t₂.positive t₃.positive
    (positive_naturality t₁ t₂ S.f hf) (positive_naturality t₂ t₃ S.g hg)
    Z hS hp₁ hp₂ hp₃ hs₁ hs₂ hs₃
  have hneg := CochainIdempotent.k0Class_shortExact S t₁.negative t₂.negative t₃.negative
    (negative_naturality t₁ t₂ S.f hf) (negative_naturality t₂ t₃ S.g hg)
    Z hS hp₁ hp₂ hp₃ hs₁ hs₂ hs₃
  unfold k0Class
  rw [hpos, hneg]
  abel

end CochainInvolution
end SerrePositivity

end InvolutionClassShortExactPart
