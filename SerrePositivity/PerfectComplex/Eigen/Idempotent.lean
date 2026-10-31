module

public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import SerrePositivity.PerfectComplex.Perfect.HomotopyCategory
public import Mathlib.Algebra.Homology.QuasiIso
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.PerfectComplex.Tensor.Perfect
public import SerrePositivity.HomologicalAlgebra.CochainIdempotentTensor

/-! # 冪等な鎖写像の像の完全性と K₀ の類

## 概要

冪等な鎖写像の像（HomologicalAlgebra/Complex/Idempotent）が完全で台を保つこと、像の台つき K₀ の類、零と恒等の場合の像と類（対合の固有空間と三次の指標の像に共通）を与える。

## 方針

像の性質は分解 `e + (1 - e) = 1` と次数ごとの直和因子から示す。

## 規約

BiproductPerfect・ClosedSupportBiproduct・FinThreeBiproduct には依存させない（refactor-plan §4.4.1 の循環の注意）。

## 使われ方

`Eigen/Involution`・`Eigen/Cubic*`、KTheory/Adams。
-/

@[expose] public noncomputable section

universe u

section IdempotentImagePerfectPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

namespace CochainIdempotent
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

lemma image_strictlyPerfect (e : CochainIdempotent K) (hK : strictlyPerfectComplex R K) :
    strictlyPerfectComplex R e.image :=
  strictlyPerfectComplex_of_degreewiseRetract e.inclusion e.projection.f
    (fun n => congrArg (fun f => f.f n) e.inclusion_projection) hK

lemma image_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (e : CochainIdempotent K) (hK : HasHomologySupportOn Z K) :
    HasHomologySupportOn Z e.image := by
  intro n
  exact (Module.support_subset_of_injective
    (HomologicalComplex.homologyMap e.inclusion n).hom
    (e.homology_inclusion_injective n)).trans (hK n)

end CochainIdempotent
end SerrePositivity

end IdempotentImagePerfectPart

section IdempotentImageClassPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CochainIdempotent
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The supported class of the image of an arbitrary idempotent. -/
abbrev k0Class (e : CochainIdempotent K) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) : K0WithSupport Z :=
  K0WithSupport.mk Z (supportedPerfectOnObj Z e.image
    (e.image_strictlyPerfect hp) (e.image_support hs))

/-- Equivariant quasi-isomorphisms preserve image classes. -/
lemma k0Class_eq_of_quasiIso (e : CochainIdempotent K) (d : CochainIdempotent L)
    (f : K ⟶ L) [QuasiIso f] (hf : e.map ≫ f = f ≫ d.map)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hpK : strictlyPerfectComplex R K) (hpL : strictlyPerfectComplex R L)
    (hsK : HasHomologySupportOn Z K) (hsL : HasHomologySupportOn Z L) :
    e.k0Class Z hpK hsK = d.k0Class Z hpL hsL := by
  have : QuasiIso (e.imageMap d f hf) := e.imageMap_quasiIso d f hf
  exact K0WithSupport.mk_eq_of_quasiIso Z e.image d.image
    (e.image_strictlyPerfect hpK) (d.image_strictlyPerfect hpL)
    (e.image_support hsK) (d.image_support hsL) (e.imageMap d f hf)

/-- The class of an idempotent image on an acyclic perfect complex is zero. -/
lemma k0Class_eq_zero_of_acyclic (e : CochainIdempotent K)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) (hK : K.Acyclic) :
    e.k0Class Z hp hs = 0 :=
  K0WithSupport.mk_eq_zero_of_acyclic Z
    (e.image_strictlyPerfect hp) (e.image_support hs) (e.image_acyclic hK)

/-- Image classes are additive on equivariant short exact sequences. -/
lemma k0Class_shortExact (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (e₁ : CochainIdempotent S.X₁) (e₂ : CochainIdempotent S.X₂) (e₃ : CochainIdempotent S.X₃)
    (hf : e₁.map ≫ S.f = S.f ≫ e₂.map) (hg : e₂.map ≫ S.g = S.g ≫ e₃.map)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (hS : S.ShortExact)
    (hp₁ : strictlyPerfectComplex R S.X₁) (hp₂ : strictlyPerfectComplex R S.X₂)
    (hp₃ : strictlyPerfectComplex R S.X₃)
    (hs₁ : HasHomologySupportOn Z S.X₁) (hs₂ : HasHomologySupportOn Z S.X₂)
    (hs₃ : HasHomologySupportOn Z S.X₃) :
    e₂.k0Class Z hp₂ hs₂ = e₁.k0Class Z hp₁ hs₁ + e₃.k0Class Z hp₃ hs₃ :=
  K0WithSupport.mk_shortExact Z (imageShortComplex S e₁ e₂ e₃ hf hg)
    (imageShortComplex_shortExact S e₁ e₂ e₃ hf hg hS)
    (e₁.image_strictlyPerfect hp₁) (e₂.image_strictlyPerfect hp₂) (e₃.image_strictlyPerfect hp₃)
    (e₁.image_support hs₁) (e₂.image_support hs₂) (e₃.image_support hs₃)

end SerrePositivity.CochainIdempotent

end IdempotentImageClassPart

section IdempotentImageTrivialPart

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-- A zero complex has zero class for any closed support containing its homology. -/
lemma K0WithSupport.mk_eq_zero_of_isZero (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) (hz : IsZero K) :
    K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) = 0 := by
  have hobj : IsZero (supportedPerfectOnObj Z K hp hs) :=
    IsZero.of_full_of_faithful_of_isZero
      (supportedPerfectOnInclusion Z ⋙ perfectHomotopyInclusion R) _
      ((homotopyQuot R).map_isZero hz)
  exact TriangulatedK0.mk_of_isZero _ hobj

end SerrePositivity

end IdempotentImageTrivialPart

