module

public import SerrePositivity.PerfectComplex.CubicActionTensor
public import SerrePositivity.PerfectComplex.CubicActionDecomposition
public import SerrePositivity.PerfectComplex.CubicActionEigenvectors
public import SerrePositivity.PerfectComplex.IdempotentTensor
public import SerrePositivity.PerfectComplex.InvolutionTensor

/-! # Nine orthogonal character projectors of a tensor product of cubic actions -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]

lemma cochainTensorMap_sum_left {J : Type*}
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (s : Finset J) (f : J → (P ⟶ P')) (g : Q ⟶ Q') :
    cochainTensorMap (∑ j ∈ s, f j) g = ∑ j ∈ s, cochainTensorMap (f j) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, cochainTensorMap_zero_left]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, cochainTensorMap_add_left, ih]

lemma cochainTensorMap_sum_right {J : Type*}
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (s : Finset J) (f : P ⟶ P') (g : J → (Q ⟶ Q')) :
    cochainTensorMap f (∑ j ∈ s, g j) = ∑ j ∈ s, cochainTensorMap f (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, cochainTensorMap_zero_right]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, cochainTensorMap_add_right, ih]

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

/-- The nine character tensor images decompose the tensor product. -/
def tensorCharacterDecompositionIso (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) :
    (⨁ fun jk : Fin 3 × Fin 3 => (τ.tensorCharacterProjector σ t ht jk).image) ≅
      cochainTensor K L :=
  CochainIdempotent.decompositionIso _ (tensorCharacterProjector_orthogonal τ σ t ht)
    (sum_tensorCharacterProjector_map τ σ t ht)

end CochainCubicAction
end SerrePositivity
