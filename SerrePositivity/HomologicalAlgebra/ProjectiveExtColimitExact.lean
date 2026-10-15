module
public import SerrePositivity.HomologicalAlgebra.ProjectiveExtSequence
public import SerrePositivity.HomologicalAlgebra.ProjectiveResolutionInjectiveAcyclic
public import SerrePositivity.HomologicalAlgebra.ExactFunctorColimits
public import SerrePositivity.HomologicalAlgebra.ProjectiveLinearCoyoneda
public import SerrePositivity.HomologicalAlgebra.KoszulDualInjectiveAcyclic

/-! # Exact coefficient models for Ext colimits and injective acyclicity -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
variable {R : Type u} [CommRing R] (X : ℕᵒᵖ ⥤ ModuleCat.{u} R)
local instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_of_univLE (ModuleCat.{u} R)

/-- Read the actual Ext colimit complex as a coefficient functor. -/
def projectiveExtColimitFunctor : ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  (projectiveExtColimitComplex X).asFunctor

instance projectiveExtColimitTerm_preservesFiniteLimits (i : ℕ) :
    PreservesFiniteLimits ((projectiveExtColimitComplex X).X i) := by
  let D := projectiveExtFunctorComplexDiagram X ⋙
    eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i
  have : ∀ n, PreservesFiniteLimits (D.obj n) := fun n => by
    change PreservesFiniteLimits (chainLinearYonedaFunctor
      (projectiveResolution (X.obj (op n))).complex ⋙ eval (ModuleCat.{u} R) (.up ℕ) i)
    infer_instance
  exact preservesFiniteLimits_of_natIso (preservesColimitIso
    (eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i)
    (projectiveExtFunctorComplexDiagram X)).symm

instance projectiveExtColimitTerm_preservesFiniteColimits (i : ℕ) :
    PreservesFiniteColimits ((projectiveExtColimitComplex X).X i) := by
  let D := projectiveExtFunctorComplexDiagram X ⋙
    eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i
  have : ∀ n, PreservesFiniteColimits (D.obj n) := fun n => by
    change PreservesFiniteColimits (chainLinearYonedaFunctor
      (projectiveResolution (X.obj (op n))).complex ⋙ eval (ModuleCat.{u} R) (.up ℕ) i)
    infer_instance
  exact preservesFiniteColimits_of_natIso (preservesColimitIso
    (eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i)
    (projectiveExtFunctorComplexDiagram X)).symm

instance projectiveExtColimitFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (projectiveExtColimitFunctor X) where
  preservesFiniteLimits J _ _ :=
    preservesLimitsOfShape_of_eval _ (fun i => by
      change PreservesLimitsOfShape J ((projectiveExtColimitComplex X).X i)
      infer_instance)

instance projectiveExtColimitFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (projectiveExtColimitFunctor X) where
  preservesFiniteColimits J _ _ :=
    preservesColimitsOfShape_of_eval _ (fun i => by
      change PreservesColimitsOfShape J ((projectiveExtColimitComplex X).X i)
      infer_instance)

/-- The actual colimit complex computes the Ext colimit in every degree. -/
def projectiveExtColimitFunctorHomologyNatIso (i : ℕ) :
    projectiveExtColimitFunctor X ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) i ≅
      colimit (inverseSystemExtDiagram X i) :=
  asFunctorCochainHomologyIso (projectiveExtColimitComplex X) i ≪≫
    projectiveExtColimitHomologyNatIso X i

/-- The actual Ext coefficient colimit has no positive homology on injectives. -/
lemma projectiveExtColimitFunctor_injective_positive_homology_isZero
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) (hi : 0 < i) :
    IsZero (((projectiveExtColimitFunctor X).obj J).homology i) := by
  let E := (projectiveExtColimitFunctorHomologyNatIso X i).app J ≪≫
    colimitObjIsoColimitCompEvaluation (inverseSystemExtDiagram X i) J
  apply IsZero.of_iso _ E
  apply sequentialModuleColimit_isZero_of_eventually_zero
  intro n
  refine ⟨n, le_refl n, ?_⟩
  have hz : IsZero (((Ext R (ModuleCat.{u} R) i).obj (op (X.obj (op n)))).obj J) :=
    IsZero.of_iso
      (projectiveResolution_injective_dual_positive_homology_isZero
        (projectiveResolution (X.obj (op n))) J i hi)
      ((projectiveResolution (X.obj (op n))).isoExt i J)
  exact hz.eq_zero_of_src _

end SerrePositivity
