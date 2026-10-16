module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues

/-! # Reversed parameter faces and their mixed degeneracy identities

All four identities are images of the usual simplex identities under rev
and the standard-simplex functor. No model structure is used.
-/

@[expose] public section
universe r
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.ReversedSimplexParameters
open HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues

def functor : SimplexCategory ⥤ SSet.{r} := SimplexCategory.rev ⋙ SSet.stdSimplex

def delta (n : ℕ) (i : Fin (n + 2)) :
    SSet.stdSimplex.{r}.obj (SimplexCategory.mk n) ⟶
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) := functor.map (SimplexCategory.δ i)

lemma delta_eq (n : ℕ) (i : Fin (n + 2)) : delta n i = SSet.stdSimplex.δ i.rev := by
  simp only [delta, functor, CategoryTheory.Functor.comp_map, SimplexCategory.rev_map_δ]
  rfl

lemma sigma_eq (n : ℕ) (i : Fin (n + 1)) : sigma n i = functor.map (SimplexCategory.σ i) := by
  simp only [sigma, functor, CategoryTheory.Functor.comp_map, SimplexCategory.rev_map_σ]

lemma delta_sigma_self (n : ℕ) (i : Fin (n + 1)) :
    delta n i.castSucc ≫ sigma n i = 𝟙 _ := by
  rw [delta, sigma_eq, ← CategoryTheory.Functor.map_comp,
    SimplexCategory.δ_comp_σ_self, CategoryTheory.Functor.map_id]
  rfl

lemma delta_sigma_succ (n : ℕ) (i : Fin (n + 1)) :
    delta n i.succ ≫ sigma n i = 𝟙 _ := by
  rw [delta, sigma_eq, ← CategoryTheory.Functor.map_comp,
    SimplexCategory.δ_comp_σ_succ, CategoryTheory.Functor.map_id]
  rfl

lemma delta_sigma_le (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    delta (n + 1) i.castSucc ≫ sigma (n + 1) j.succ = sigma n j ≫ delta n i := by
  rw [delta, delta, sigma_eq, sigma_eq, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, SimplexCategory.δ_comp_σ_of_le h]

lemma delta_sigma_gt (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    delta (n + 1) i.succ ≫ sigma (n + 1) j.castSucc = sigma n j ≫ delta n i := by
  rw [delta, delta, sigma_eq, sigma_eq, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, SimplexCategory.δ_comp_σ_of_gt h]

end SerrePositivity.SimplicialModel.ReversedSimplexParameters
