module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleResolution
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Tensor an unresolved module with one fixed chain complex -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Vary the unresolved module, while keeping the entire chain complex fixed. -/
def moduleTensorChainFunctor (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj N := ((tensorLeft N).mapHomologicalComplex (.down ℕ)).obj K
  map f := (NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat R)).map f) (.down ℕ)).app K
  map_id N := by
    rw [CategoryTheory.Functor.map_id, NatTrans.mapHomologicalComplex_id]
    rfl
  map_comp f g := by
    rw [CategoryTheory.Functor.map_comp, NatTrans.mapHomologicalComplex_comp]
    rfl

/-- Each term of this functor is the original tensor functor with that fixed module. -/
def moduleTensorChainEvalIso (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    moduleTensorChainFunctor K ⋙ eval (ModuleCat R) (.down ℕ) n ≅
      (tensoringRight (ModuleCat R)).obj (K.X n) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp; rfl)

end SerrePositivity
