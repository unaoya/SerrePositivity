module
public import SerrePositivity.HomologicalAlgebra.ExactFunctorColimits
public import SerrePositivity.HomologicalAlgebra.ProjectiveLinearCoyoneda
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyKoszulComparison

/-! # Exactness in coefficients of the actual dual Koszul colimit -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R] {e : ℕ} (z : Fin e → R)

local instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_of_univLE (ModuleCat.{u} R)

/-- Each actual dual Koszul stage is exact in arbitrary coefficient modules. -/
instance koszulDualModuleFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (koszulDualModuleFunctor z) := by
  have : ∀ i, Projective ((toChain (koszulComplex z)).X i) := fun i =>
    Projective.of_iso ((koszulComplex z).restrictionXIso embUp rfl).symm
      (koszulComplex_projective_X z _)
  exact chainLinearYonedaFunctor_preservesFiniteColimits _

/-- Each actual colimit term preserves finite limits in its coefficients. -/
instance koszulDualColimitTerm_preservesFiniteLimits (i : ℕ) :
    PreservesFiniteLimits ((koszulDualColimitComplex z).X i) := by
  let D := koszulDualFunctorComplexDiagram z ⋙
    eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i
  have : ∀ n, PreservesFiniteLimits (D.obj n) := fun n => by
    change PreservesFiniteLimits (koszulDualModuleFunctor (fun j => z j ^ n) ⋙
      eval (ModuleCat.{u} R) (.up ℕ) i)
    infer_instance
  exact preservesFiniteLimits_of_natIso (preservesColimitIso
    (eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i)
    (koszulDualFunctorComplexDiagram z)).symm

/-- Each actual colimit term preserves finite colimits in its coefficients. -/
instance koszulDualColimitTerm_preservesFiniteColimits (i : ℕ) :
    PreservesFiniteColimits ((koszulDualColimitComplex z).X i) := by
  let D := koszulDualFunctorComplexDiagram z ⋙
    eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i
  have : ∀ n, PreservesFiniteColimits (D.obj n) := fun n => by
    change PreservesFiniteColimits (koszulDualModuleFunctor (fun j => z j ^ n) ⋙
      eval (ModuleCat.{u} R) (.up ℕ) i)
    infer_instance
  exact preservesFiniteColimits_of_natIso (preservesColimitIso
    (eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i)
    (koszulDualFunctorComplexDiagram z)).symm

/-- The entire actual dual-colimit complex functor preserves finite limits. -/
instance koszulDualColimitFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (koszulDualColimitFunctor z) where
  preservesFiniteLimits J _ _ :=
    preservesLimitsOfShape_of_eval _ (fun i => by
      change PreservesLimitsOfShape J ((koszulDualColimitComplex z).X i)
      infer_instance)

/-- The entire actual dual-colimit complex functor preserves finite colimits. -/
instance koszulDualColimitFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (koszulDualColimitFunctor z) where
  preservesFiniteColimits J _ _ :=
    preservesColimitsOfShape_of_eval _ (fun i => by
      change PreservesColimitsOfShape J ((koszulDualColimitComplex z).X i)
      infer_instance)

/-- Actual short exact coefficient sequences give short exact sequences of the actual colimits. -/
lemma koszulDualColimitFunctor_shortExact (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) : (S.map (koszulDualColimitFunctor z)).ShortExact :=
  by
    have := hS.mono_f
    have := hS.epi_g
    exact hS.map (koszulDualColimitFunctor z)

end SerrePositivity
