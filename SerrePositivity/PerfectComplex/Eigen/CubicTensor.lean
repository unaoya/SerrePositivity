module

public import SerrePositivity.PerfectComplex.Eigen.Cubic
public import SerrePositivity.PerfectComplex.Tensor.Perfect
public import SerrePositivity.PerfectComplex.Eigen.Idempotent
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import SerrePositivity.PerfectComplex.Eigen.CubicClass
public import SerrePositivity.PerfectComplex.FinThreeBiproduct

/-! # 三次の作用のテンソルと K₀ の類のたたみ込み

## 概要

三次の鎖作用のテンソル積と、その九つの直交する指標の射影、指標の和による三つの行への分け方、テンソルの固有空間が指標の合う三つのテンソル積の和であること、テンソルの固有空間の K₀ の類のたたみ込みの公式を与える。

## 方針

九つの射影を指標の和で三つずつまとめ、行ごとに類を比べる。

## 規約

指標の射影は `Eigen/Cubic` のもの。

## 使われ方

KTheory/Adams の三乗の作用素の乗法性。
-/

@[expose] public noncomputable section

universe u v

section CubicActionTensorPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]
namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Simultaneously act on the two tensor factors. -/
def tensor (τ : CochainCubicAction K) (σ : CochainCubicAction L) :
    CochainCubicAction (cochainTensor K L) where
  map := cochainTensorMap τ.map σ.map
  cube := by
    rw [cochainTensorMap_comp, cochainTensorMap_comp, τ.cube, σ.cube, cochainTensorMap_id]

end CochainCubicAction
end SerrePositivity

end CubicActionTensorPart

section CubicActionTensorProjectorsPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]

namespace CochainCubicAction
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ} [Invertible (3 : R)]

lemma eigenvector_comp_projectorMap_eq_zero (τ : CochainCubicAction K)
    (a b : R) (hb : b ^ 3 = 1) (f : M ⟶ K) (hf : f ≫ τ.map = a • f)
    (hab : IsUnit (a - b)) : f ≫ τ.projectorMap b = 0 := by
  have he : a • (f ≫ τ.projectorMap b) = b • (f ≫ τ.projectorMap b) := by
    calc
      _ = (f ≫ τ.map) ≫ τ.projectorMap b := by rw [hf, Linear.smul_comp]
      _ = _ := by rw [Category.assoc, map_comp_projectorMap τ b hb, Linear.comp_smul]
  have hz : (a - b) • (f ≫ τ.projectorMap b) = 0 := by rw [sub_smul, sub_eq_zero, he]
  apply hab.smul_left_cancel.mp
  simpa only [smul_zero] using hz

/-- Tensor the j and k character projectors, retaining both indices. -/
def tensorCharacterProjector (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (jk : Fin 3 × Fin 3) :
    CochainIdempotent (cochainTensor K L) :=
  CochainIdempotent.tensor
    (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) jk.1)
    (σ.characterProjector t (cube_eq_one_of_cubic_relation t ht) jk.2)

@[simp]
lemma tensorCharacterProjector_map (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (jk : Fin 3 × Fin 3) :
    (τ.tensorCharacterProjector σ t ht jk).map =
      cochainTensorMap (τ.projectorMap (cubicCharacter t jk.1))
        (σ.projectorMap (cubicCharacter t jk.2)) := rfl

lemma tensorCharacterProjector_orthogonal (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (i j : Fin 3 × Fin 3) (hne : i ≠ j) :
    (τ.tensorCharacterProjector σ t ht i).map ≫
      (τ.tensorCharacterProjector σ t ht j).map = 0 := by
  rw [tensorCharacterProjector_map, tensorCharacterProjector_map, cochainTensorMap_comp]
  by_cases h₁ : i.1 = j.1
  · have h₂ : i.2 ≠ j.2 := fun h₂ => hne (Prod.ext h₁ h₂)
    rw [projectorMap_orthogonal σ _ _
      (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) i.2)
      (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) j.2)
      (cubicCharacter_difference_isUnit t ht i.2 j.2 h₂), cochainTensorMap_zero_right]
  · rw [projectorMap_orthogonal τ _ _
      (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) i.1)
      (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) j.1)
      (cubicCharacter_difference_isUnit t ht i.1 j.1 h₁), cochainTensorMap_zero_left]

lemma sum_tensorCharacterProjector_map (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) :
    ∑ jk : Fin 3 × Fin 3, (τ.tensorCharacterProjector σ t ht jk).map = 𝟙 _ := by
  rw [Fintype.sum_prod_type]
  simp_rw [tensorCharacterProjector_map, ← cochainTensorMap_sum_right]
  rw [← cochainTensorMap_sum_left, sum_character_projectorMap τ t ht,
    sum_character_projectorMap σ t ht, cochainTensorMap_id]

@[reassoc]
lemma tensorCharacterProjector_eigen (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (jk : Fin 3 × Fin 3) :
    (τ.tensorCharacterProjector σ t ht jk).map ≫ (τ.tensor σ).map =
      cubicCharacter t (jk.1 + jk.2) • (τ.tensorCharacterProjector σ t ht jk).map := by
  rw [tensorCharacterProjector_map]
  change cochainTensorMap (τ.projectorMap (cubicCharacter t jk.1))
      (σ.projectorMap (cubicCharacter t jk.2)) ≫ cochainTensorMap τ.map σ.map = _
  rw [cochainTensorMap_comp,
    projectorMap_comp_map τ _ (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) jk.1),
    projectorMap_comp_map σ _ (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) jk.2),
    cochainTensorMap_smul_left, cochainTensorMap_smul_right, smul_smul,
    cubicCharacter_mul t (cube_eq_one_of_cubic_relation t ht)]

end CochainCubicAction
end SerrePositivity

end CubicActionTensorProjectorsPart

section CubicActionTensorRowsPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]

private lemma nine_sum_by_character {G : Type*} [AddCommMonoid G]
    (f : Fin 3 × Fin 3 → G) (l : Fin 3) :
    (∑ jk : Fin 3 × Fin 3, if jk.1 + jk.2 = l then f jk else 0) =
      ∑ i : Fin 3, f (i, l - i) := by
  have h₁ : -(1 : Fin 3) = 2 := by decide
  have h₂ : -(2 : Fin 3) = 1 := by decide
  fin_cases l <;> simp [Fintype.sum_prod_type, Fin.sum_univ_three, h₁, h₂]

namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} [Invertible (3 : R)]

lemma tensorCharacterProjector_comp_projectorMap
    (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (jk : Fin 3 × Fin 3) (l : Fin 3) :
    (τ.tensorCharacterProjector σ t ht jk).map ≫
      (τ.tensor σ).projectorMap (cubicCharacter t l) =
        if jk.1 + jk.2 = l then (τ.tensorCharacterProjector σ t ht jk).map else 0 := by
  classical
  by_cases h : jk.1 + jk.2 = l
  · rw [ite_eq_left h]
    apply eigenvector_comp_projectorMap
    · exact cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) l
    · simpa only [h] using tensorCharacterProjector_eigen τ σ t ht jk
  · rw [ite_eq_right h]
    exact eigenvector_comp_projectorMap_eq_zero (τ.tensor σ) _ _
      (cubicCharacter_cube t (cube_eq_one_of_cubic_relation t ht) l) _
      (tensorCharacterProjector_eigen τ σ t ht jk)
      (cubicCharacter_difference_isUnit t ht (jk.1 + jk.2) l h)

/-- The j and l-j parts contribute to the l character of the tensor action. -/
abbrev tensorCharacterRowProjector (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (l i : Fin 3) :=
  τ.tensorCharacterProjector σ t ht (i, l - i)

lemma tensorCharacterRowProjector_orthogonal
    (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (l i j : Fin 3) (hij : i ≠ j) :
    (τ.tensorCharacterRowProjector σ t ht l i).map ≫
      (τ.tensorCharacterRowProjector σ t ht l j).map = 0 :=
  tensorCharacterProjector_orthogonal τ σ t ht _ _
    (fun h => hij (congrArg Prod.fst h))

lemma sum_tensorCharacterRowProjector_map
    (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (l : Fin 3) :
    (∑ i : Fin 3, (τ.tensorCharacterRowProjector σ t ht l i).map) =
      ((τ.tensor σ).characterProjector t (cube_eq_one_of_cubic_relation t ht) l).map := by
  classical
  calc
    _ = ∑ jk : Fin 3 × Fin 3,
        if jk.1 + jk.2 = l then (τ.tensorCharacterProjector σ t ht jk).map else 0 :=
      (nine_sum_by_character (fun jk => (τ.tensorCharacterProjector σ t ht jk).map) l).symm
    _ = ∑ jk : Fin 3 × Fin 3, (τ.tensorCharacterProjector σ t ht jk).map ≫
        (τ.tensor σ).projectorMap (cubicCharacter t l) := by
      apply Finset.sum_congr rfl
      intro jk _
      exact (tensorCharacterProjector_comp_projectorMap τ σ t ht jk l).symm
    _ = _ := by
      rw [← sum_comp, sum_tensorCharacterProjector_map, id_comp]
      rfl

end CochainCubicAction
end SerrePositivity

end CubicActionTensorRowsPart

section CubicActionTensorEigenPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The three row projector images form one eigenspace of the tensor action. -/
def tensorCharacterRowDecompositionIso (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (l : Fin 3) :
    (⨁ fun i : Fin 3 => (τ.tensorCharacterRowProjector σ t ht l i).image) ≅
      ((τ.tensor σ).characterProjector t (cube_eq_one_of_cubic_relation t ht) l).image :=
  CochainIdempotent.imageFiniteSumIso _ _
    (tensorCharacterRowProjector_orthogonal τ σ t ht l)
    (sum_tensorCharacterRowProjector_map τ σ t ht l)

/-- Sum the j and l-j eigenspace tensor products to obtain the l eigenspace. -/
def tensorCharacterEigenIso (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (l : Fin 3) :
    (⨁ fun i : Fin 3 => cochainTensor
      (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) i).image
      (σ.characterProjector t (cube_eq_one_of_cubic_relation t ht) (l - i)).image) ≅
        ((τ.tensor σ).characterProjector t (cube_eq_one_of_cubic_relation t ht) l).image :=
  biproduct.mapIso (fun i : Fin 3 => CochainIdempotent.imageTensorIso
    (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) i)
    (σ.characterProjector t (cube_eq_one_of_cubic_relation t ht) (l - i))) ≪≫
      tensorCharacterRowDecompositionIso τ σ t ht l

end CochainCubicAction
end SerrePositivity

end CubicActionTensorEigenPart

section CubicActionTensorClassPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

lemma eigenK0Class_tensor (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0)
    (Y Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hpK : strictlyPerfectComplex R K) (hpL : strictlyPerfectComplex R L)
    (hsK : HasHomologySupportOn Y K) (hsL : HasHomologySupportOn Z L) (l : Fin 3) :
    (τ.tensor σ).eigenK0Class t ht (Y ⊓ Z)
      (strictlyPerfectComplex_cochainTensor K L hpK hpL) (hsK.cochainTensor hsL hpK hpL) l =
      ∑ i : Fin 3, K0WithSupport.cup (τ.eigenK0Class t ht Y hpK hsK i)
        (σ.eigenK0Class t ht Z hpL hsL (l - i)) := by
  let a := fun i => τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) i
  let b := fun i => σ.characterProjector t (cube_eq_one_of_cubic_relation t ht) i
  let W := fun i : Fin 3 => cochainTensor (a i).image (b (l - i)).image
  have hpW : ∀ i, strictlyPerfectComplex R (W i) := fun i =>
    strictlyPerfectComplex_cochainTensor _ _ ((a i).image_strictlyPerfect hpK)
      ((b (l - i)).image_strictlyPerfect hpL)
  have hsW : ∀ i, HasHomologySupportOn (Y ⊓ Z) (W i) := fun i =>
    ((a i).image_support hsK).cochainTensor ((b (l - i)).image_support hsL)
      ((a i).image_strictlyPerfect hpK) ((b (l - i)).image_strictlyPerfect hpL)
  let d := (τ.tensor σ).characterProjector t (cube_eq_one_of_cubic_relation t ht) l
  have hd := d.image_strictlyPerfect (strictlyPerfectComplex_cochainTensor K L hpK hpL)
  have sd := d.image_support (hsK.cochainTensor hsL hpK hpL)
  have h := K0WithSupport.mk_eq_of_quasiIso (Y ⊓ Z) (⨁ W) d.image
    (cochainFinThreeBiproduct_perfect W hpW) hd (cochainFinThreeBiproduct_support W hsW) sd
    (tensorCharacterEigenIso τ σ t ht l).hom
  change K0WithSupport.mk (Y ⊓ Z) (supportedPerfectOnObj (Y ⊓ Z) d.image hd sd) = _
  rw [← h, K0WithSupport.mk_finThreeBiproduct (Y ⊓ Z) W hpW hsW]
  apply Finset.sum_congr rfl
  intro i _
  exact K0WithSupport.mk_tensor (a i).image (b (l - i)).image
    ((a i).image_strictlyPerfect hpK) ((b (l - i)).image_strictlyPerfect hpL)
    ((a i).image_support hsK) ((b (l - i)).image_support hsL)

/-- Weighted tensor eigenspaces multiply by character convolution. -/
lemma weightedK0Class_tensor (E : Type v) [CommRing E]
    (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (Y Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hpK : strictlyPerfectComplex R K) (hpL : strictlyPerfectComplex R L)
    (hsK : HasHomologySupportOn Y K) (hsL : HasHomologySupportOn Z L) :
    (τ.tensor σ).weightedK0Class E t ht ζ (Y ⊓ Z)
      (strictlyPerfectComplex_cochainTensor K L hpK hpL) (hsK.cochainTensor hsL hpK hpL) =
      K0WithSupport.coefficientCup E (τ.weightedK0Class E t ht ζ Y hpK hsK)
        (σ.weightedK0Class E t ht ζ Z hpL hsL) := by
  classical
  unfold weightedK0Class
  simp_rw [eigenK0Class_tensor τ σ t ht Y Z hpK hpL hsK hsL,
    TensorProduct.tmul_sum]
  rw [Finset.sum_comm]
  simp only [map_sum, LinearMap.sum_apply, K0WithSupport.coefficientCup_tmul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  symm
  apply Fintype.sum_equiv (Equiv.addLeft i)
  intro j
  change (cubicCharacter ζ i * cubicCharacter ζ j) ⊗ₜ[ℤ]
    K0WithSupport.cup (τ.eigenK0Class t ht Y hpK hsK i)
      (σ.eigenK0Class t ht Z hpL hsL j) =
    cubicCharacter ζ (i + j) ⊗ₜ[ℤ]
      K0WithSupport.cup (τ.eigenK0Class t ht Y hpK hsK i)
        (σ.eigenK0Class t ht Z hpL hsL (i + j - i))
  rw [add_sub_cancel_left]
  rw [cubicCharacter_mul ζ (cube_eq_one_of_cubic_relation ζ hζ)]

end CochainCubicAction
end SerrePositivity

end CubicActionTensorClassPart
