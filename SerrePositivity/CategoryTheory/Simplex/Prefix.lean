module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-! # Add one initial vertex to a simplex, with explicit maps -/

@[expose] public section
open CategoryTheory

namespace SerrePositivity.SimplexPrefix

def map {n m : SimplexCategory} (f : n ⟶ m) :
    SimplexCategory.mk (n.len + 1) ⟶ SimplexCategory.mk (m.len + 1) :=
  SimplexCategory.Hom.mk ⟨Fin.cases 0 (fun i => (f.toOrderHom i).succ), by
    intro i j hij
    induction i using Fin.cases with
    | zero => exact Fin.zero_le _
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        exact Fin.succ_le_succ_iff.mpr
          (f.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hij))⟩

def functor : SimplexCategory ⥤ SimplexCategory where
  obj n := SimplexCategory.mk (n.len + 1)
  map := map
  map_id n := by
    ext i : 3
    induction i using Fin.cases <;> rfl
  map_comp f g := by
    ext i : 3
    induction i using Fin.cases <;> rfl

lemma map_δ {n : ℕ} (i : Fin (n + 2)) :
    functor.map (SimplexCategory.δ i) = SimplexCategory.δ i.succ := by
  ext j : 3
  induction j using Fin.cases with
  | zero =>
    change 0 = i.succ.succAbove 0
    exact (Fin.succ_succAbove_zero i).symm
  | succ j =>
    change (i.succAbove j).succ = i.succ.succAbove j.succ
    exact (Fin.succ_succAbove_succ i j).symm

lemma map_σ {n : ℕ} (i : Fin (n + 1)) :
    functor.map (SimplexCategory.σ i) = SimplexCategory.σ i.succ := by
  ext j : 3
  induction j using Fin.cases with
  | zero =>
    change 0 = i.succ.predAbove 0
    simp [Fin.predAbove]
  | succ j =>
    change (i.predAbove j).succ = i.succ.predAbove j.succ
    exact (Fin.succ_predAbove_succ i j).symm

end SerrePositivity.SimplexPrefix
