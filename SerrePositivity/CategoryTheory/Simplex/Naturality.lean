module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-! # Assemble a simplicial natural transformation from its face and degeneracy squares -/

@[expose] public section
universe v u
open CategoryTheory

namespace SerrePositivity.SimplexNaturality
variable {C : Type u} [Category.{v} C] (F G : SimplicialObject C)
  (app : ∀ n : SimplexCategoryᵒᵖ, F.obj n ⟶ G.obj n)

def property : MorphismProperty SimplexCategory := fun X Y f =>
  F.map f.op ≫ app (Opposite.op X) = app (Opposite.op Y) ≫ G.map f.op

instance : (property F G app).IsMultiplicative where
  id_mem X := by simp [property]
  comp_mem f g hf hg := by
    dsimp only [property] at hf hg ⊢
    rw [op_comp, F.map_comp, G.map_comp, Category.assoc, hf, ← Category.assoc, hg,
      Category.assoc]

lemma naturality
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), F.δ i ≫ app (Opposite.op (SimplexCategory.mk n)) =
      app (Opposite.op (SimplexCategory.mk (n + 1))) ≫ G.δ i)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), F.σ i ≫
      app (Opposite.op (SimplexCategory.mk (n + 1))) =
        app (Opposite.op (SimplexCategory.mk n)) ≫ G.σ i)
    {X Y : SimplexCategoryᵒᵖ} (f : X ⟶ Y) : F.map f ≫ app Y = app X ≫ G.map f := by
  have htop : property F G app = ⊤ :=
    SimplexCategory.morphismProperty_eq_top _ hδ hσ
  have hf : property F G app f.unop := by rw [htop]; trivial
  exact hf

def ofFacesDegeneracies
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), F.δ i ≫ app (Opposite.op (SimplexCategory.mk n)) =
      app (Opposite.op (SimplexCategory.mk (n + 1))) ≫ G.δ i)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), F.σ i ≫
      app (Opposite.op (SimplexCategory.mk (n + 1))) =
        app (Opposite.op (SimplexCategory.mk n)) ≫ G.σ i) : F ⟶ G where
  app := app
  naturality _ _ f := naturality F G app hδ hσ f

lemma ofFacesDegeneracies_app
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), F.δ i ≫ app (Opposite.op (SimplexCategory.mk n)) =
      app (Opposite.op (SimplexCategory.mk (n + 1))) ≫ G.δ i)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), F.σ i ≫
      app (Opposite.op (SimplexCategory.mk (n + 1))) =
        app (Opposite.op (SimplexCategory.mk n)) ≫ G.σ i)
    (n : SimplexCategoryᵒᵖ) : (ofFacesDegeneracies F G app hδ hσ).app n = app n := rfl

end SerrePositivity.SimplexNaturality
