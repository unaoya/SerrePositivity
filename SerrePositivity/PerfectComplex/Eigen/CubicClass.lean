module

public import SerrePositivity.PerfectComplex.Eigen.Cubic
public import SerrePositivity.KTheory.Coefficients
public import SerrePositivity.PerfectComplex.Eigen.Idempotent
public import Mathlib.Algebra.Homology.QuasiIso
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import SerrePositivity.PerfectComplex.BiproductPerfect

/-! # 三次の固有空間の重み付き類

## 概要

係数を拡大した三次の固有空間の重み付きの K₀ の類を定め、同型での不変性と非輪状な場合の消滅、同変な短完全列での加法性、二項和・スカラー作用・自明な作用の指標の類を与える。

## 方針

類は指標の像の類に 1 の三乗根の重みを掛けた和で定める。

## 規約

`cubicCharacter t j := t ^ j` は `AddChar.zmodChar 3 ht j` で置き換えられる（確度中、refactor-plan §4.4.2）。

## 使われ方

KTheory/Adams の三乗の Adams 作用素の重み。
-/

@[expose] public noncomputable section

universe u v

section CubicActionClassPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace CochainCubicAction
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The integer K₀ class of one character eigenspace. -/
def eigenK0Class (τ : CochainCubicAction K) (t : R) (ht : t ^ 2 + t + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) (j : Fin 3) :
    K0WithSupport Z :=
  (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).k0Class Z hp hs

/-- The ambient root determines the eigenspaces; the coefficient root weights their classes. -/
def weightedK0Class (E : Type v) [CommRing E]
    (τ : CochainCubicAction K) (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    K0WithSupport.Coefficients E Z :=
  ∑ j : Fin 3, cubicCharacter ζ j ⊗ₜ[ℤ] τ.eigenK0Class t ht Z hp hs j

end CochainCubicAction
end SerrePositivity

end CubicActionClassPart

section CubicActionClassMapsPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

lemma eigenK0Class_eq_of_quasiIso (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (f : K ⟶ L) [QuasiIso f] (hf : τ.map ≫ f = f ≫ σ.map)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hpK : strictlyPerfectComplex R K) (hpL : strictlyPerfectComplex R L)
    (hsK : HasHomologySupportOn Z K) (hsL : HasHomologySupportOn Z L) (j : Fin 3) :
    τ.eigenK0Class t ht Z hpK hsK j = σ.eigenK0Class t ht Z hpL hsL j := by
  let e := τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j
  let d := σ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j
  let he := τ.projectorMap_naturality σ f hf (cubicCharacter t j)
  exact e.k0Class_eq_of_quasiIso d f he Z hpK hpL hsK hsL

lemma weightedK0Class_eq_of_quasiIso (E : Type v) [CommRing E]
    (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (f : K ⟶ L) [QuasiIso f] (hf : τ.map ≫ f = f ≫ σ.map)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hpK : strictlyPerfectComplex R K) (hpL : strictlyPerfectComplex R L)
    (hsK : HasHomologySupportOn Z K) (hsL : HasHomologySupportOn Z L) :
    τ.weightedK0Class E t ht ζ Z hpK hsK = σ.weightedK0Class E t ht ζ Z hpL hsL := by
  unfold weightedK0Class
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun x => cubicCharacter ζ j ⊗ₜ[ℤ] x)
    (eigenK0Class_eq_of_quasiIso τ σ f hf t ht Z hpK hpL hsK hsL j)

lemma eigenK0Class_eq_zero_of_acyclic (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K)
    (hac : K.Acyclic) (j : Fin 3) : τ.eigenK0Class t ht Z hp hs j = 0 := by
  let e := τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j
  exact e.k0Class_eq_zero_of_acyclic Z hp hs hac

lemma weightedK0Class_eq_zero_of_acyclic (E : Type v) [CommRing E]
    (τ : CochainCubicAction K) (t : R) (ht : t ^ 2 + t + 1 = 0)
    (ζ : E) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) (hac : K.Acyclic) :
    τ.weightedK0Class E t ht ζ Z hp hs = 0 := by
  unfold weightedK0Class
  simp only [eigenK0Class_eq_zero_of_acyclic τ t ht Z hp hs hac,
    TensorProduct.tmul_zero, Finset.sum_const_zero]

end CochainCubicAction
end SerrePositivity

end CubicActionClassMapsPart

section CubicActionShortExactPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace CochainCubicAction
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
variable (τ₁ : CochainCubicAction S.X₁) (τ₂ : CochainCubicAction S.X₂)
    (τ₃ : CochainCubicAction S.X₃)
variable (hf : τ₁.map ≫ S.f = S.f ≫ τ₂.map) (hg : τ₂.map ≫ S.g = S.g ≫ τ₃.map)
variable (t : R) (ht : t ^ 2 + t + 1 = 0)

include hf hg in
lemma eigenK0Class_shortExact
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (j : Fin 3) (hS : S.ShortExact)
    (hp₁ : strictlyPerfectComplex R S.X₁) (hp₂ : strictlyPerfectComplex R S.X₂)
    (hp₃ : strictlyPerfectComplex R S.X₃)
    (hs₁ : HasHomologySupportOn Z S.X₁) (hs₂ : HasHomologySupportOn Z S.X₂)
    (hs₃ : HasHomologySupportOn Z S.X₃) :
    τ₂.eigenK0Class t ht Z hp₂ hs₂ j =
      τ₁.eigenK0Class t ht Z hp₁ hs₁ j + τ₃.eigenK0Class t ht Z hp₃ hs₃ j := by
  exact CochainIdempotent.k0Class_shortExact S
    (τ₁.characterProjector t (cube_eq_one_of_cubic_relation t ht) j)
    (τ₂.characterProjector t (cube_eq_one_of_cubic_relation t ht) j)
    (τ₃.characterProjector t (cube_eq_one_of_cubic_relation t ht) j)
    (τ₁.projectorMap_naturality τ₂ S.f hf (cubicCharacter t j))
    (τ₂.projectorMap_naturality τ₃ S.g hg (cubicCharacter t j))
    Z hS hp₁ hp₂ hp₃ hs₁ hs₂ hs₃

include hf hg in
lemma weightedK0Class_shortExact (E : Type v) [CommRing E] (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (hS : S.ShortExact)
    (hp₁ : strictlyPerfectComplex R S.X₁) (hp₂ : strictlyPerfectComplex R S.X₂)
    (hp₃ : strictlyPerfectComplex R S.X₃)
    (hs₁ : HasHomologySupportOn Z S.X₁) (hs₂ : HasHomologySupportOn Z S.X₂)
    (hs₃ : HasHomologySupportOn Z S.X₃) :
    τ₂.weightedK0Class E t ht ζ Z hp₂ hs₂ =
      τ₁.weightedK0Class E t ht ζ Z hp₁ hs₁ + τ₃.weightedK0Class E t ht ζ Z hp₃ hs₃ := by
  unfold weightedK0Class
  simp_rw [eigenK0Class_shortExact S τ₁ τ₂ τ₃ hf hg t ht Z _ hS hp₁ hp₂ hp₃ hs₁ hs₂ hs₃]
  simp only [TensorProduct.tmul_add, Finset.sum_add_distrib]

end CochainCubicAction
end SerrePositivity

end CubicActionShortExactPart

section CubicActionBiproductClassPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R]
namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

variable [Invertible (3 : R)]

lemma eigenK0Class_biprod (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (j : Fin 3)
    (hp : strictlyPerfectComplex R K) (hq : strictlyPerfectComplex R L)
    (hs : HasHomologySupportOn Z K) (hs' : HasHomologySupportOn Z L) :
    (τ.biprod σ).eigenK0Class t ht Z (strictlyPerfectComplex_biprod hp hq) (hs.biprod hs') j =
      τ.eigenK0Class t ht Z hp hs j + σ.eigenK0Class t ht Z hq hs' j := by
  let S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
    ShortComplex.mk (Limits.biprod.inl : K ⟶ K ⊞ L) Limits.biprod.snd (by simp)
  let spl : S.Splitting := ShortComplex.Splitting.ofHasBinaryBiproduct K L
  exact eigenK0Class_shortExact S τ (τ.biprod σ) σ
    (by simp [S, biprod]) (by simp [S, biprod]) t ht Z j spl.shortExact
    hp (strictlyPerfectComplex_biprod hp hq) hq hs (hs.biprod hs') hs'

lemma weightedK0Class_biprod (E : Type v) [CommRing E]
    (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hq : strictlyPerfectComplex R L)
    (hs : HasHomologySupportOn Z K) (hs' : HasHomologySupportOn Z L) :
    (τ.biprod σ).weightedK0Class E t ht ζ Z (strictlyPerfectComplex_biprod hp hq)
        (hs.biprod hs') =
      τ.weightedK0Class E t ht ζ Z hp hs + σ.weightedK0Class E t ht ζ Z hq hs' := by
  unfold weightedK0Class
  simp_rw [eigenK0Class_biprod τ σ t ht Z _ hp hq hs hs']
  simp only [tmul_add, Finset.sum_add_distrib]

end CochainCubicAction
end SerrePositivity

end CubicActionBiproductClassPart

section CubicActionScalarClassPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R]
namespace CochainCubicAction
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

variable [Invertible (3 : R)]

lemma characterProjector_self_of_map_eq_scalar (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 3 = 1) (j : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K) :
    (τ.characterProjector t ht j).map = 𝟙 K := by
  have hf : (𝟙 K : K ⟶ K) ≫ τ.map = cubicCharacter t j • 𝟙 K := by
    rw [id_comp, hτ]
  change τ.projectorMap (cubicCharacter t j) = 𝟙 K
  simpa only [id_comp] using τ.eigenvector_comp_projectorMap
    (cubicCharacter t j) (cubicCharacter_cube t ht j) (𝟙 K) hf

lemma characterProjector_other_of_map_eq_scalar (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (j k : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K) (hne : j ≠ k) :
    (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) k).map = 0 := by
  have he := τ.characterProjector_orthogonal t ht j k hne
  rw [characterProjector_self_of_map_eq_scalar τ t
    (cube_eq_one_of_cubic_relation t ht) j hτ, id_comp] at he
  exact he

/-- The matching character image of a scalar action is the original complex. -/
def characterSelfImageIsoOfMapEqScalar (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 3 = 1) (j : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K) :
    (τ.characterProjector t ht j).image ≅ K :=
  (τ.characterProjector t ht j).imageIsoOfMapEqId
    (characterProjector_self_of_map_eq_scalar τ t ht j hτ)

lemma characterOtherImage_isZero_of_map_eq_scalar (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (j k : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K) (hne : j ≠ k) :
    IsZero (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) k).image :=
  (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) k).image_isZero_of_map_eq_zero
    (characterProjector_other_of_map_eq_scalar τ t ht j k hτ hne)

lemma eigenK0Class_self_of_map_eq_scalar (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (j : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    τ.eigenK0Class t ht Z hp hs j = K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) :=
  K0WithSupport.mk_eq_of_quasiIso Z _ _
    ((τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image_strictlyPerfect hp) hp
    ((τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image_support hs) hs
    (characterSelfImageIsoOfMapEqScalar τ t (cube_eq_one_of_cubic_relation t ht) j hτ).hom

lemma eigenK0Class_other_of_map_eq_scalar (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (j k : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K)
    (hne : j ≠ k) : τ.eigenK0Class t ht Z hp hs k = 0 := by
  let e := τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) k
  have hz := characterOtherImage_isZero_of_map_eq_scalar τ t ht j k hτ hne
  exact K0WithSupport.mk_eq_zero_of_isZero Z (e.image_strictlyPerfect hp) (e.image_support hs) hz

lemma weightedK0Class_of_map_eq_scalar (E : Type v) [CommRing E] (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (j : Fin 3)
    (hτ : τ.map = cubicCharacter t j • 𝟙 K) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    τ.weightedK0Class E t ht ζ Z hp hs =
      cubicCharacter ζ j ⊗ₜ[ℤ] K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) := by
  unfold weightedK0Class
  rw [Finset.sum_eq_single j]
  · rw [eigenK0Class_self_of_map_eq_scalar τ t ht j hτ Z hp hs]
  · intro k _ hkj
    rw [eigenK0Class_other_of_map_eq_scalar τ t ht j k hτ Z hp hs hkj.symm, tmul_zero]
  · simp

/-- A character scalar action contributes just its character times the original class. -/
@[simp]
lemma weightedK0Class_characterScalar (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (j : Fin 3) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    (characterScalar K t (cube_eq_one_of_cubic_relation t ht) j).weightedK0Class
        E t ht ζ Z hp hs =
      cubicCharacter ζ j ⊗ₜ[ℤ] K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) :=
  weightedK0Class_of_map_eq_scalar E _ t ht j rfl ζ Z hp hs

end CochainCubicAction
end SerrePositivity

end CubicActionScalarClassPart

section CubicActionIdentityClassPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace CochainCubicAction
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

lemma weightedK0Class_of_map_eq_id (E : Type v) [CommRing E] (τ : CochainCubicAction K)
    (hτ : τ.map = 𝟙 K) (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) :
    τ.weightedK0Class E t ht ζ Z hp hs =
      (1 : E) ⊗ₜ[ℤ] K0WithSupport.mk Z (supportedPerfectOnObj Z K hp hs) := by
  simpa only [cubicCharacter, Fin.val_zero, pow_zero] using
    weightedK0Class_of_map_eq_scalar E τ t ht 0 (by simpa [cubicCharacter] using hτ) ζ Z hp hs

end CochainCubicAction
end SerrePositivity

end CubicActionIdentityClassPart
