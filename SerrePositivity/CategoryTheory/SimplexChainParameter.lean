module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! # The actual first-vertex parameter of a chain of simplex operators

All vertices come from the same first simplex by the actual prefix maps.
Restriction factors through the prefix leading to the new first simplex.
-/

@[expose] public section
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplexChainParameter
variable {n : ℕ} (c : Fin (n + 1) ⥤ SimplexCategoryᵒᵖ)

lemma prefix_comp {i j : Fin (n + 1)} (h : i ≤ j) :
    c.map (homOfLE (Fin.zero_le j)) =
      c.map (homOfLE (Fin.zero_le i)) ≫ c.map (homOfLE h) :=
  c.map_comp _ _

abbrev vertex (i : Fin (n + 1)) : Fin ((c.obj 0).unop.len + 1) :=
  (c.map (homOfLE (Fin.zero_le i))).unop.toOrderHom 0

lemma monotone : Monotone (vertex c) := by
  intro i j h
  have e := congrArg (fun f => f.unop.toOrderHom 0) (prefix_comp c h)
  change vertex c j = (c.map (homOfLE (Fin.zero_le i))).unop.toOrderHom
    ((c.map (homOfLE h)).unop.toOrderHom 0) at e
  rw [e]
  exact (c.map (homOfLE (Fin.zero_le i))).unop.toOrderHom.monotone (Fin.zero_le _)

def parameter : SimplexCategory.mk n ⟶ (c.obj 0).unop :=
  SimplexCategory.Hom.mk ⟨vertex c, monotone c⟩

lemma parameter_apply (i : Fin (n + 1)) :
    (parameter c).toOrderHom i = vertex c i := rfl

lemma reindex {m : ℕ} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    θ ≫ parameter c =
      parameter ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
        (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))).unop := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  exact congrArg (fun f => f.unop.toOrderHom 0)
    (prefix_comp c (θ.toOrderHom.monotone (Fin.zero_le i)))

end SerrePositivity.SimplexChainParameter
