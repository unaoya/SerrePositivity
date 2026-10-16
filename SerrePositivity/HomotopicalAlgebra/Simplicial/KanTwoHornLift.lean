module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-! # Fill a specified outer two-horn over its specified base triangle

Both given whole edges and the given base triangle are retained. Only
the original horn right lifting class is assumed, not a model structure.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.KanTwoHornLift
variable {E B : SSet.{v}} (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)

include hp in
lemma exists_triangle
    (e₀ e₁ : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ E)
    (b : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ B)
    (hc : SSet.stdSimplex.δ (0 : Fin 2) ≫ e₀ = SSet.stdSimplex.δ (0 : Fin 2) ≫ e₁)
    (h₀ : e₀ ≫ p = SSet.stdSimplex.δ (0 : Fin 3) ≫ b)
    (h₁ : e₁ ≫ p = SSet.stdSimplex.δ (1 : Fin 3) ≫ b) :
    ∃ t : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ E,
      SSet.stdSimplex.δ (0 : Fin 3) ≫ t = e₀ ∧
      SSet.stdSimplex.δ (1 : Fin 3) ≫ t = e₁ ∧ t ≫ p = b := by
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff p).mpr hp
  let fs : ∀ (j : Fin 3) (_ : j ≠ 2),
      SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ E := fun j _ => if j = 0 then e₀ else e₁
  have hf : SSet.horn.IsCompatible fs := by
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> first
    | exact (hj rfl).elim
    | exact (hk rfl).elim
    | exact ((not_lt_of_ge (by decide)) hjk).elim
    | exact hc
  have hb : ∀ j hj, fs j hj ≫ p = SSet.stdSimplex.δ j ≫ b := by
    intro j hj
    fin_cases j <;> first | exact (hj rfl).elim | exact h₀ | exact h₁
  obtain ⟨t, ht, hb⟩ := hf.exists_lift p b hb
  exact ⟨t, ht 0 (by decide), ht 1 (by decide), hb⟩

end SerrePositivity.SimplicialModel.KanTwoHornLift
