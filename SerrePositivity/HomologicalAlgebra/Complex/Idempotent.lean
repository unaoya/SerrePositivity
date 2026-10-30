module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # 冪等な鎖写像の像と直和分解

## 概要

冪等な鎖写像 e の像 `image`（恒等写像と e の等化子）と標準の包含・射影を作り、同変な鎖写像が像の間の写像を誘導すること、直交する冪等元の有限族による直和分解と補空間、像の和、関手による像の移送、像の同型、像が非輪状性・擬同型・短完全列・次数ごとの有限性や射影性を保つこと、零と恒等の場合の像を与える。

## 方針

像は Mathlib の等化子で作り、分解は包含と射影の合成の和が恒等になることから示す。擬同型の保存は `quasiIso_of_retractArrow` による。

## 規約

冪等鎖写像の像と分解は Mathlib への提出候補。

## 使われ方

PerfectComplex の対合・三次の作用の固有分解、KTheory/Adams。
-/

@[expose] public noncomputable section

universe u

section CochainIdempotentPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

/-- An idempotent endomorphism of a cochain complex. -/
structure CochainIdempotent (K : CochainComplex (ModuleCat.{u} R) ℤ) where
  map : K ⟶ K
  idem : map ≫ map = map

namespace CochainIdempotent
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The image of an idempotent chain map. -/
abbrev image (e : CochainIdempotent K) := equalizer (𝟙 K) e.map

/-- The image embeds in the original complex. -/
abbrev inclusion (e : CochainIdempotent K) : e.image ⟶ K := equalizer.ι (𝟙 K) e.map

/-- The idempotent, regarded as a map onto its image. -/
def projection (e : CochainIdempotent K) : K ⟶ e.image :=
  equalizer.lift e.map (by rw [comp_id, e.idem])

@[simp, reassoc]
lemma projection_inclusion (e : CochainIdempotent K) :
    e.projection ≫ e.inclusion = e.map := equalizer.lift_ι _ _

@[simp, reassoc]
lemma inclusion_map (e : CochainIdempotent K) :
    e.inclusion ≫ e.map = e.inclusion := by
  simpa using (equalizer.condition (𝟙 K) e.map).symm

@[simp, reassoc]
lemma inclusion_projection (e : CochainIdempotent K) :
    e.inclusion ≫ e.projection = 𝟙 e.image := by
  apply (cancel_mono e.inclusion).1
  simp only [Category.assoc, projection_inclusion, inclusion_map, id_comp]

/-- A chain map commuting with two idempotents restricts to their images. -/
def imageMap (e : CochainIdempotent K) (d : CochainIdempotent L) (f : K ⟶ L)
    (hf : e.map ≫ f = f ≫ d.map) : e.image ⟶ d.image :=
  equalizer.lift (e.inclusion ≫ f) (by
    rw [comp_id, Category.assoc, ← hf, ← Category.assoc, inclusion_map])

@[simp, reassoc]
lemma imageMap_inclusion (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ⟶ L) (hf : e.map ≫ f = f ≫ d.map) :
    imageMap e d f hf ≫ d.inclusion = e.inclusion ≫ f := equalizer.lift_ι _ _

@[reassoc]
lemma projection_imageMap (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ⟶ L) (hf : e.map ≫ f = f ≫ d.map) :
    e.projection ≫ imageMap e d f hf = f ≫ d.projection := by
  apply (cancel_mono d.inclusion).1
  simp only [Category.assoc, imageMap_inclusion, projection_inclusion_assoc,
    projection_inclusion, hf]

@[simp]
lemma imageMap_id (e : CochainIdempotent K) :
    imageMap e e (𝟙 K) (by simp) = 𝟙 e.image := by
  apply (cancel_mono e.inclusion).1
  simp

end CochainIdempotent
end SerrePositivity

end CochainIdempotentPart

section CochainIdempotentHomologyPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

namespace CochainIdempotent
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

@[simp, reassoc]
lemma inclusion_projection_f (e : CochainIdempotent K) (n : ℤ) :
    e.inclusion.f n ≫ e.projection.f n = 𝟙 (e.image.X n) := by
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
    congrArg (fun f => f.f n) e.inclusion_projection

@[simp, reassoc]
lemma homology_inclusion_projection (e : CochainIdempotent K) (n : ℤ) :
    HomologicalComplex.homologyMap e.inclusion n ≫
      HomologicalComplex.homologyMap e.projection n = 𝟙 (e.image.homology n) := by
  rw [← HomologicalComplex.homologyMap_comp, e.inclusion_projection,
    HomologicalComplex.homologyMap_id]

lemma homology_inclusion_injective (e : CochainIdempotent K) (n : ℤ) :
    Function.Injective (HomologicalComplex.homologyMap e.inclusion n).hom := by
  intro x y h
  have hx := congrArg (fun f => f.hom x) (e.homology_inclusion_projection n)
  have hy := congrArg (fun f => f.hom y) (e.homology_inclusion_projection n)
  exact hx.symm.trans ((congrArg (HomologicalComplex.homologyMap e.projection n).hom h).trans hy)

end CochainIdempotent
end SerrePositivity

end CochainIdempotentHomologyPart

section CochainIdempotentAcyclicPart

namespace SerrePositivity.CochainIdempotent
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R] {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Homology of an idempotent image is a retract of the original homology. -/
lemma image_acyclic (e : CochainIdempotent K) (hK : K.Acyclic) : e.image.Acyclic := by
  intro n
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ n).mpr
  rw [IsZero.iff_id_eq_zero, ← e.homology_inclusion_projection n]
  rw [(hK n).isZero_homology.eq_of_tgt (homologyMap e.inclusion n) 0, zero_comp]

end SerrePositivity.CochainIdempotent

end CochainIdempotentAcyclicPart

section CochainIdempotentDecompositionPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]

namespace CochainIdempotent
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Orthogonal idempotents have zero cross-component maps. -/
lemma inclusion_projection_eq_zero (e d : CochainIdempotent K)
    (h : e.map ≫ d.map = 0) : e.inclusion ≫ d.projection = 0 := by
  apply (cancel_mono d.inclusion).1
  rw [Category.assoc, projection_inclusion, zero_comp]
  rw [← e.inclusion_map, Category.assoc, h, comp_zero]

/-- The images of a finite orthogonal family summing to the identity decompose the complex. -/
def decompositionIso {J : Type} [Fintype J] (e : J → CochainIdempotent K)
    (horth : ∀ i j, i ≠ j → (e i).map ≫ (e j).map = 0)
    (hsum : ∑ j, (e j).map = 𝟙 K) : (⨁ fun j => (e j).image) ≅ K where
  hom := biproduct.desc fun j => (e j).inclusion
  inv := biproduct.lift fun j => (e j).projection
  hom_inv_id := by
    classical
    apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro i
    by_cases h : i = j
    · subst j
      simp
    · simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
        id_comp, biproduct.ι_π_ne _ h]
      exact inclusion_projection_eq_zero (e i) (e j) (horth i j h)
  inv_hom_id := by
    rw [biproduct.lift_desc]
    simpa only [projection_inclusion] using hsum

@[simp, reassoc]
lemma ι_decompositionIso_hom {J : Type} [Fintype J] (e : J → CochainIdempotent K)
    (horth : ∀ i j, i ≠ j → (e i).map ≫ (e j).map = 0)
    (hsum : ∑ j, (e j).map = 𝟙 K) (j : J) :
    biproduct.ι (fun j => (e j).image) j ≫ (decompositionIso e horth hsum).hom =
      (e j).inclusion := biproduct.ι_desc _ _

@[simp, reassoc]
lemma decompositionIso_inv_π {J : Type} [Fintype J] (e : J → CochainIdempotent K)
    (horth : ∀ i j, i ≠ j → (e i).map ≫ (e j).map = 0)
    (hsum : ∑ j, (e j).map = 𝟙 K) (j : J) :
    (decompositionIso e horth hsum).inv ≫ biproduct.π (fun j => (e j).image) j =
      (e j).projection := biproduct.lift_π _ _

/-- The complementary idempotent. -/
def complement (e : CochainIdempotent K) : CochainIdempotent K where
  map := 𝟙 K - e.map
  idem := Idempotents.idem_of_id_sub_idem e.map e.idem

@[simp]
lemma map_comp_complement (e : CochainIdempotent K) : e.map ≫ e.complement.map = 0 := by
  simp [complement, comp_sub, e.idem]

@[simp]
lemma complement_comp_map (e : CochainIdempotent K) : e.complement.map ≫ e.map = 0 := by
  simp [complement, sub_comp, e.idem]

@[simp]
lemma map_add_complement (e : CochainIdempotent K) : e.map + e.complement.map = 𝟙 K := by
  simp [complement]

/-- An idempotent and its complement split the original complex as a binary biproduct. -/
def complementIso (e : CochainIdempotent K) : e.image ⊞ e.complement.image ≅ K where
  hom := biprod.desc e.inclusion e.complement.inclusion
  inv := biprod.lift e.projection e.complement.projection
  hom_inv_id := by
    apply biprod.hom_ext
    · apply biprod.hom_ext'
      · simp
      · simp [inclusion_projection_eq_zero e.complement e (complement_comp_map e)]
    · apply biprod.hom_ext'
      · simp [inclusion_projection_eq_zero e e.complement (map_comp_complement e)]
      · simp
  inv_hom_id := by
    rw [biprod.lift_desc, projection_inclusion, projection_inclusion, map_add_complement]

end CochainIdempotent
end SerrePositivity

end CochainIdempotentDecompositionPart

section CochainIdempotentSumPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]
namespace CochainIdempotent
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

@[ext]
lemma ext {e d : CochainIdempotent K} (h : e.map = d.map) : e = d := by
  cases e
  cases d
  cases h
  rfl

@[reassoc]
lemma image_eqToIso_inclusion {e d : CochainIdempotent K} (h : e = d) :
    (eqToIso (congrArg image h)).hom ≫ d.inclusion = e.inclusion := by
  cases h
  simp

def orthogonalSum (e d : CochainIdempotent K)
    (hed : e.map ≫ d.map = 0) (hde : d.map ≫ e.map = 0) : CochainIdempotent K where
  map := e.map + d.map
  idem := by simp [Preadditive.add_comp, Preadditive.comp_add, e.idem, d.idem, hed, hde]

@[reassoc]
lemma inclusion_orthogonalSum_map_left (e d : CochainIdempotent K)
    (hed : e.map ≫ d.map = 0) (hde : d.map ≫ e.map = 0) :
    e.inclusion ≫ (orthogonalSum e d hed hde).map = e.inclusion := by
  change e.inclusion ≫ (e.map + d.map) = _
  rw [Preadditive.comp_add, inclusion_map]
  have hz : e.inclusion ≫ d.map = 0 := by
    rw [← e.inclusion_map, Category.assoc, hed, comp_zero]
  rw [hz, add_zero]

@[reassoc]
lemma inclusion_orthogonalSum_map_right (e d : CochainIdempotent K)
    (hed : e.map ≫ d.map = 0) (hde : d.map ≫ e.map = 0) :
    d.inclusion ≫ (orthogonalSum e d hed hde).map = d.inclusion := by
  change d.inclusion ≫ (e.map + d.map) = _
  rw [Preadditive.comp_add, inclusion_map]
  have hz : d.inclusion ≫ e.map = 0 := by
    rw [← d.inclusion_map, Category.assoc, hde, comp_zero]
  rw [hz, zero_add]

def imageOrthogonalSumIso (e d : CochainIdempotent K)
    (hed : e.map ≫ d.map = 0) (hde : d.map ≫ e.map = 0) :
    e.image ⊞ d.image ≅ (orthogonalSum e d hed hde).image where
  hom := biprod.desc e.inclusion d.inclusion ≫ (orthogonalSum e d hed hde).projection
  inv := (orthogonalSum e d hed hde).inclusion ≫ biprod.lift e.projection d.projection
  hom_inv_id := by
    apply biprod.hom_ext
    · apply biprod.hom_ext'
      · simp [Category.assoc, projection_inclusion_assoc (orthogonalSum e d hed hde),
          inclusion_orthogonalSum_map_left_assoc e d hed hde]
      · simp [Category.assoc, projection_inclusion_assoc (orthogonalSum e d hed hde),
          inclusion_orthogonalSum_map_right_assoc e d hed hde,
          inclusion_projection_eq_zero d e hde]
    · apply biprod.hom_ext'
      · simp [Category.assoc, projection_inclusion_assoc (orthogonalSum e d hed hde),
          inclusion_orthogonalSum_map_left_assoc e d hed hde,
          inclusion_projection_eq_zero e d hed]
      · simp [Category.assoc, projection_inclusion_assoc (orthogonalSum e d hed hde),
          inclusion_orthogonalSum_map_right_assoc e d hed hde]
  inv_hom_id := by
    change (orthogonalSum e d hed hde).inclusion ≫
      (biprod.lift e.projection d.projection ≫ biprod.desc e.inclusion d.inclusion) ≫
      (orthogonalSum e d hed hde).projection = _
    rw [biprod.lift_desc, projection_inclusion, projection_inclusion]
    change (orthogonalSum e d hed hde).inclusion ≫ (orthogonalSum e d hed hde).map ≫
      (orthogonalSum e d hed hde).projection = _
    rw [← Category.assoc, inclusion_map, inclusion_projection]

@[reassoc]
lemma imageOrthogonalSumIso_hom_inclusion (e d : CochainIdempotent K)
    (hed : e.map ≫ d.map = 0) (hde : d.map ≫ e.map = 0) :
    (imageOrthogonalSumIso e d hed hde).hom ≫ (orthogonalSum e d hed hde).inclusion =
      biprod.desc e.inclusion d.inclusion := by
  change (biprod.desc e.inclusion d.inclusion ≫ (orthogonalSum e d hed hde).projection) ≫
    (orthogonalSum e d hed hde).inclusion = _
  rw [Category.assoc, projection_inclusion]
  apply biprod.hom_ext'
  · simp [inclusion_orthogonalSum_map_left]
  · simp [inclusion_orthogonalSum_map_right]

end CochainIdempotent
end SerrePositivity

end CochainIdempotentSumPart

section CochainIdempotentFiniteSumPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]
namespace CochainIdempotent
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}
variable {J : Type} [Fintype J] (e : J → CochainIdempotent K) (d : CochainIdempotent K)
variable (horth : ∀ i j, i ≠ j → (e i).map ≫ (e j).map = 0)
variable (hsum : ∑ j, (e j).map = d.map)

include horth hsum in
lemma map_comp_finiteSum (j : J) : (e j).map ≫ d.map = (e j).map := by
  classical
  rw [← hsum, comp_sum]
  rw [Finset.sum_eq_single j]
  · exact (e j).idem
  · intro b _ hb
    exact horth j b (Ne.symm hb)
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

include horth hsum in
@[reassoc]
lemma inclusion_finiteSum_map (j : J) : (e j).inclusion ≫ d.map = (e j).inclusion := by
  rw [← (e j).inclusion_map, Category.assoc, map_comp_finiteSum e d horth hsum]

/-- The images of orthogonal idempotents summing to d decompose the image of d. -/
def imageFiniteSumIso : (⨁ fun j => (e j).image) ≅ d.image where
  hom := biproduct.desc (fun j => (e j).inclusion) ≫ d.projection
  inv := d.inclusion ≫ biproduct.lift (fun j => (e j).projection)
  hom_inv_id := by
    classical
    apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro i
    by_cases h : i = j
    · subst j
      simp [Category.assoc, projection_inclusion_assoc d,
        inclusion_finiteSum_map_assoc e d horth hsum]
    · simp only [Category.assoc, projection_inclusion_assoc, biproduct.lift_π,
        biproduct.ι_desc_assoc, inclusion_finiteSum_map_assoc e d horth hsum,
        id_comp, biproduct.ι_π_ne _ h]
      exact inclusion_projection_eq_zero (e i) (e j) (horth i j h)
  inv_hom_id := by
    change d.inclusion ≫
      (biproduct.lift (fun j => (e j).projection) ≫
        biproduct.desc (fun j => (e j).inclusion)) ≫ d.projection = 𝟙 _
    rw [biproduct.lift_desc]
    simp only [projection_inclusion]
    rw [hsum, ← Category.assoc, inclusion_map, inclusion_projection]

@[reassoc]
lemma imageFiniteSumIso_hom_inclusion :
    (imageFiniteSumIso e d horth hsum).hom ≫ d.inclusion =
      biproduct.desc (fun j => (e j).inclusion) := by
  rw [imageFiniteSumIso, Category.assoc, projection_inclusion]
  apply biproduct.hom_ext'
  intro j
  simp only [biproduct.ι_desc_assoc, biproduct.ι_desc]
  exact inclusion_finiteSum_map e d horth hsum j

end CochainIdempotent
end SerrePositivity

end CochainIdempotentFiniteSumPart

section CochainIdempotentIsoPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]
namespace CochainIdempotent
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

lemma equivariance_inv (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ≅ L) (h : e.map ≫ f.hom = f.hom ≫ d.map) :
    d.map ≫ f.inv = f.inv ≫ e.map := by
  have hz : f.inv ≫ e.map ≫ f.hom = d.map := by
    rw [h, Iso.inv_hom_id_assoc]
  exact (Iso.comp_inv_eq f).mpr (by simpa only [Category.assoc] using hz.symm)

def imageIso (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ≅ L) (h : e.map ≫ f.hom = f.hom ≫ d.map) : e.image ≅ d.image where
  hom := imageMap e d f.hom h
  inv := imageMap d e f.inv (equivariance_inv e d f h)
  hom_inv_id := by
    apply (cancel_mono e.inclusion).mp
    simp [Category.assoc, imageMap_inclusion, imageMap_inclusion_assoc]
  inv_hom_id := by
    apply (cancel_mono d.inclusion).mp
    simp [Category.assoc, imageMap_inclusion, imageMap_inclusion_assoc]

@[reassoc]
lemma imageIso_hom_inclusion (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ≅ L) (h : e.map ≫ f.hom = f.hom ≫ d.map) :
    (imageIso e d f h).hom ≫ d.inclusion = e.inclusion ≫ f.hom :=
  imageMap_inclusion e d f.hom h

end CochainIdempotent
end SerrePositivity

end CochainIdempotentIsoPart

section CochainIdempotentFunctorPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R S : Type u} [CommRing R] [CommRing S]
namespace CochainIdempotent
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}
variable (F : CochainComplex (ModuleCat.{u} R) ℤ ⥤
  CochainComplex (ModuleCat.{u} S) ℤ) (e : CochainIdempotent K)

/-- A functor transports the idempotence equation. -/
def mapFunctor : CochainIdempotent (F.obj K) where
  map := F.map e.map
  idem := by rw [← F.map_comp, e.idem]

/-- Split images are preserved without an assumption about general equalizers. -/
def imageFunctorIso : F.obj e.image ≅ (mapFunctor F e).image where
  hom := F.map e.inclusion ≫ (mapFunctor F e).projection
  inv := (mapFunctor F e).inclusion ≫ F.map e.projection
  hom_inv_id := by
    simp only [Category.assoc, projection_inclusion_assoc]
    change F.map e.inclusion ≫ F.map e.map ≫ F.map e.projection = _
    rw [← F.map_comp_assoc, inclusion_map, ← F.map_comp, inclusion_projection,
      F.map_id]
  inv_hom_id := by
    rw [Category.assoc, ← F.map_comp_assoc, projection_inclusion]
    change (mapFunctor F e).inclusion ≫ (mapFunctor F e).map ≫
      (mapFunctor F e).projection = _
    rw [inclusion_map_assoc, inclusion_projection]

@[reassoc]
lemma imageFunctorIso_hom_inclusion :
    (imageFunctorIso F e).hom ≫ (mapFunctor F e).inclusion = F.map e.inclusion := by
  change F.map e.inclusion ≫ (mapFunctor F e).projection ≫
    (mapFunctor F e).inclusion = _
  rw [projection_inclusion]
  change F.map e.inclusion ≫ F.map e.map = _
  rw [← F.map_comp, inclusion_map]

@[reassoc]
lemma map_projection_imageFunctorIso_hom :
    F.map e.projection ≫ (imageFunctorIso F e).hom = (mapFunctor F e).projection := by
  change F.map e.projection ≫ F.map e.inclusion ≫ (mapFunctor F e).projection = _
  rw [← F.map_comp_assoc, projection_inclusion]
  change (mapFunctor F e).map ≫ (mapFunctor F e).projection = _
  rw [← projection_inclusion, Category.assoc, inclusion_projection, comp_id]

/-- Equivariant maps remain equivariant after applying a functor. -/
lemma mapFunctor_equivariance {L : CochainComplex (ModuleCat.{u} R) ℤ}
    (d : CochainIdempotent L) (f : K ⟶ L) (hf : e.map ≫ f = f ≫ d.map) :
    (mapFunctor F e).map ≫ F.map f = F.map f ≫ (mapFunctor F d).map := by
  change F.map e.map ≫ F.map f = F.map f ≫ F.map d.map
  rw [← F.map_comp, hf, F.map_comp]

@[reassoc]
lemma imageFunctorIso_naturality {L : CochainComplex (ModuleCat.{u} R) ℤ}
    (d : CochainIdempotent L) (f : K ⟶ L) (hf : e.map ≫ f = f ≫ d.map) :
    F.map (imageMap e d f hf) ≫ (imageFunctorIso F d).hom =
      (imageFunctorIso F e).hom ≫
        imageMap (mapFunctor F e) (mapFunctor F d) (F.map f)
          (mapFunctor_equivariance F e d f hf) := by
  apply (cancel_mono (mapFunctor F d).inclusion).mp
  simp only [Category.assoc, imageFunctorIso_hom_inclusion,
    imageMap_inclusion, imageFunctorIso_hom_inclusion_assoc]
  rw [← F.map_comp, imageMap_inclusion, F.map_comp]

/-- Compare the transported image with any projector having the same underlying map. -/
def imageFunctorIsoOfMapEq (d : CochainIdempotent (F.obj K)) (h : F.map e.map = d.map) :
    F.obj e.image ≅ d.image :=
  imageFunctorIso F e ≪≫ imageIso _ _ (Iso.refl _) (by
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [comp_id, id_comp]
    exact h)

@[reassoc]
lemma imageFunctorIsoOfMapEq_hom_inclusion
    (d : CochainIdempotent (F.obj K)) (h : F.map e.map = d.map) :
    (imageFunctorIsoOfMapEq F e d h).hom ≫ d.inclusion = F.map e.inclusion := by
  simp only [imageFunctorIsoOfMapEq, Iso.trans_hom, Category.assoc,
    imageIso_hom_inclusion, Iso.refl_hom, comp_id, imageFunctorIso_hom_inclusion]

end CochainIdempotent
end SerrePositivity

end CochainIdempotentFunctorPart

section CochainIdempotentQuasiIsoPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

namespace CochainIdempotent
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The restriction of an equivariant map is a retract of that map in the arrow category. -/
def imageMapRetract (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ⟶ L) (hf : e.map ≫ f = f ≫ d.map) :
    RetractArrow (imageMap e d f hf) f where
  i := Arrow.homMk e.inclusion d.inclusion (imageMap_inclusion e d f hf).symm
  r := Arrow.homMk e.projection d.projection (projection_imageMap e d f hf)
  retract := by
    apply Arrow.hom_ext <;> simp

/-- Equivariant quasi-isomorphisms restrict to quasi-isomorphisms of idempotent images. -/
lemma imageMap_quasiIso (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ⟶ L) (hf : e.map ≫ f = f ≫ d.map) [QuasiIso f] :
    QuasiIso (imageMap e d f hf) :=
  quasiIso_of_retractArrow (imageMapRetract e d f hf)

end CochainIdempotent
end SerrePositivity

end CochainIdempotentQuasiIsoPart

section CochainIdempotentShortExactPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

namespace CochainIdempotent
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
  (e₁ : CochainIdempotent S.X₁) (e₂ : CochainIdempotent S.X₂) (e₃ : CochainIdempotent S.X₃)
  (hf : e₁.map ≫ S.f = S.f ≫ e₂.map) (hg : e₂.map ≫ S.g = S.g ≫ e₃.map)

/-- A short complex restricts to compatible idempotent images. -/
def imageShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (imageMap e₁ e₂ S.f hf) (imageMap e₂ e₃ S.g hg) (by
    apply (cancel_mono e₃.inclusion).1
    simp only [Category.assoc, imageMap_inclusion, imageMap_inclusion_assoc, S.zero,
      comp_zero, zero_comp])

/-- The restricted short complex is a retract of the original one. -/
def imageShortComplexRetract : Retract (imageShortComplex S e₁ e₂ e₃ hf hg) S where
  i := {
    τ₁ := e₁.inclusion
    τ₂ := e₂.inclusion
    τ₃ := e₃.inclusion
    comm₁₂ := (imageMap_inclusion e₁ e₂ S.f hf).symm
    comm₂₃ := (imageMap_inclusion e₂ e₃ S.g hg).symm }
  r := {
    τ₁ := e₁.projection
    τ₂ := e₂.projection
    τ₃ := e₃.projection
    comm₁₂ := projection_imageMap e₁ e₂ S.f hf
    comm₂₃ := projection_imageMap e₂ e₃ S.g hg }
  retract := by
    apply ShortComplex.hom_ext <;> simp [imageShortComplex]

/-- Exactness is preserved by restriction to compatible idempotent images. -/
lemma imageShortComplex_exact (hS : S.Exact) : (imageShortComplex S e₁ e₂ e₃ hf hg).Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  have h := (imageShortComplexRetract S e₁ e₂ e₃ hf hg).map
    (ShortComplex.homologyFunctor (CochainComplex (ModuleCat.{u} R) ℤ))
  change IsZero ((ShortComplex.homologyFunctor
    (CochainComplex (ModuleCat.{u} R) ℤ)).obj (imageShortComplex S e₁ e₂ e₃ hf hg))
  rw [IsZero.iff_id_eq_zero, ← h.retract]
  have hz : IsZero ((ShortComplex.homologyFunctor
    (CochainComplex (ModuleCat.{u} R) ℤ)).obj S) :=
    (ShortComplex.exact_iff_isZero_homology S).mp hS
  rw [hz.eq_of_tgt h.i 0, zero_comp]

/-- Short exactness is preserved by restriction to compatible idempotent images. -/
lemma imageShortComplex_shortExact (hS : S.ShortExact) :
    (imageShortComplex S e₁ e₂ e₃ hf hg).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact {
    mono_f := (MorphismProperty.monomorphisms _).of_retract
      (imageMapRetract e₁ e₂ S.f hf) inferInstance
    epi_g := (MorphismProperty.epimorphisms _).of_retract
      (imageMapRetract e₂ e₃ S.g hg) inferInstance
    exact := imageShortComplex_exact S e₁ e₂ e₃ hf hg hS.exact }

end CochainIdempotent
end SerrePositivity

end CochainIdempotentShortExactPart

section CochainIdempotentTrivialPart

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

namespace CochainIdempotent

/-- The image of the identity projector is canonically the original complex. -/
def imageIsoOfMapEqId (e : CochainIdempotent K) (he : e.map = 𝟙 K) : e.image ≅ K where
  hom := e.inclusion
  inv := e.projection
  hom_inv_id := e.inclusion_projection
  inv_hom_id := e.projection_inclusion.trans he

@[simp]
lemma imageIsoOfMapEqId_hom (e : CochainIdempotent K) (he : e.map = 𝟙 K) :
    (e.imageIsoOfMapEqId he).hom = e.inclusion := rfl

@[simp]
lemma imageIsoOfMapEqId_inv (e : CochainIdempotent K) (he : e.map = 𝟙 K) :
    (e.imageIsoOfMapEqId he).inv = e.projection := rfl

/-- The image of the zero projector is a zero complex. -/
lemma image_isZero_of_map_eq_zero (e : CochainIdempotent K) (he : e.map = 0) :
    IsZero e.image := by
  have hi : e.inclusion = 0 := by
    rw [← e.inclusion_map, he, comp_zero]
  rw [IsZero.iff_id_eq_zero, ← e.inclusion_projection, hi, zero_comp]

end CochainIdempotent
end SerrePositivity

end CochainIdempotentTrivialPart
