module

public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Cofibrant objects under a left Quillen left adjoint -/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {D : Type u'} [Category.{v'} D] [ModelCategory D]

lemma isCofibrant_obj (L : C ⥤ D) [L.IsLeftAdjoint] [IsLeftQuillen L]
    (X : C) [IsCofibrant X] : IsCofibrant (L.obj X) := by
  have : Cofibration (L.map (initial.to X)) := map_cofibration L (initial.to X)
  exact (isCofibrant_iff_of_isInitial (L.map (initial.to X))
    (initialIsInitial.isInitialObj L (⊥_ C))).mpr inferInstance

end SerrePositivity.Quillen
