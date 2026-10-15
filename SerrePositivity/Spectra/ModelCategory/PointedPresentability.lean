module

public import SerrePositivity.Spectra.ModelCategory.PointedGenerators
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLimits
public import SerrePositivity.HomotopicalAlgebra.Smith.ConservativeAdjunction
public import Mathlib.CategoryTheory.Presentable.Type

/-! # Local presentability of the actual pointed simplicial base

Simplicial sets are a small functor category in Type. The faithful and
conservative pointed forgetful functor is accessible and has the actual
free-basepoint left adjoint, so the proved transport theorem applies.
No model structure is required for this categorical fact.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModelInputs
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

lemma pointedSimplicial_isLocallyPresentable :
    IsLocallyPresentable.{u} PointedSimplicialSet.{u} := by
  have : IsLocallyPresentable.{u} SSet.{u} :=
    Smith.AccessibleLimits.functorCategory_isLocallyPresentable.{u} (C := Type u) SimplexCategoryᵒᵖ
  have := pointedForget_accessible.{u}
  have : PointedSimplicialSet.forget.{u}.IsAccessible.{u} :=
    Functor.isAccessible_of_isCardinalAccessible _ Cardinal.aleph0.{u}
  exact Smith.ConservativeAdjunction.isLocallyPresentable
    (PointedObject.adjoinForgetAdjunction (C := SSet.{u}))

end SerrePositivity.SimplicialModelInputs
