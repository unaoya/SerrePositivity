module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preorder

/-! # Constant colimits over an index with a least element -/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.ColimitFromBottom
variable (K : Type w) [Preorder K] [OrderBot K] {C : Type u} [Category.{v} C]

lemma const_ι_isIso (X : C) [HasColimit ((Functor.const K).obj X)] :
    IsIso (colimit.ι ((Functor.const K).obj X) ⊥) := by
  have : ∀ (i j : K) (f : i ⟶ j), IsIso (((Functor.const K).obj X).map f) :=
    fun _ _ _ => inferInstanceAs (IsIso (𝟙 X))
  exact isIso_ι_of_isInitial isInitialBot ((Functor.const K).obj X)

variable [ModelCategory C] [HasColimitsOfShape K C]

lemma weakEquivalence_const_map {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C ((colim : (K ⥤ C) ⥤ C).map ((Functor.const K).map f)) := by
  have := const_ι_isIso K X
  have := const_ι_isIso K Y
  have hiX := (weakEquivalences C).of_isIso (colimit.ι ((Functor.const K).obj X) ⊥)
  have hiY := (weakEquivalences C).of_isIso (colimit.ι ((Functor.const K).obj Y) ⊥)
  have hn := colimit.ι_map ((Functor.const K).map f) ⊥
  exact (weakEquivalences C).of_precomp _ _ hiX
    (hn.symm ▸ (weakEquivalences C).comp_mem _ _ hf hiY)

end SerrePositivity.DiagramModel.ColimitFromBottom
