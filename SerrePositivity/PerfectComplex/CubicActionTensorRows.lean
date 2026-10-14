module

public import SerrePositivity.PerfectComplex.CubicActionTensorProjectors

/-! # Grouping the nine tensor projectors by the sum of their characters -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
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
