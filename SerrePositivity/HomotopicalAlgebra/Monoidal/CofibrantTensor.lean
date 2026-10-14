module

public import SerrePositivity.HomotopicalAlgebra.Monoidal.ModelCategory
public import SerrePositivity.CategoryTheory.Monoidal.TensorPowers
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Cofibrant objects and tensor powers in monoidal model categories -/

@[expose] public section
universe u v u' v'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MonoidalCategory

namespace SerrePositivity.Quillen

lemma map_isCofibrant {C : Type u} [Category.{v} C] [ModelCategory C]
    {D : Type u'} [Category.{v'} D] [ModelCategory D]
    (L : C ⥤ D) [L.IsLeftAdjoint] [IsLeftQuillen L] (X : C) [IsCofibrant X] :
    IsCofibrant (L.obj X) := by
  have := map_cofibration L (initial.to X)
  exact (isCofibrant_iff_of_isInitial (L.map (initial.to X))
    (initialIsInitial.isInitialObj L (⊥_ C))).2 inferInstance

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [IsQuillenBifunctor (curriedTensor C)]

lemma tensorLeft_isLeftQuillen (X : C) [IsCofibrant X] : IsLeftQuillen (tensorLeft X) := by
  have : ∀ Y : C, ((curriedTensor C).flip.obj Y).IsLeftAdjoint :=
    fun Y ↦ inferInstanceAs (tensorRight Y).IsLeftAdjoint
  exact isLeftQuillen_obj_of_cofibrant (curriedTensor C) X

lemma tensor_isCofibrant (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    IsCofibrant (X ⊗ Y) := by
  have := tensorLeft_isLeftQuillen X
  exact map_isCofibrant (tensorLeft X) Y

lemma tensorPower_isCofibrant (X : C) [IsCofibrant X] [IsCofibrant (𝟙_ C)] (n : ℕ) :
    IsCofibrant (TensorPowers.power X n) := by
  induction n with
  | zero => exact inferInstanceAs (IsCofibrant (𝟙_ C))
  | succ n ih =>
    have := ih
    exact tensor_isCofibrant X (TensorPowers.power X n)
end SerrePositivity.Quillen
