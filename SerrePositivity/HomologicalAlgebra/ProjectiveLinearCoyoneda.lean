module
public import SerrePositivity.HomologicalAlgebra.ChainLinearYoneda
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Yoneda
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Exact coefficient functors of degreewise projective chain complexes -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Linear Hom out of any fixed module preserves limits in its coefficient variable. -/
instance linearCoyonedaModule_preservesLimits (P : ModuleCat.{u} R) :
    PreservesLimits ((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)) := by
  have : PreservesLimits (((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)) ⋙
      forget (ModuleCat.{u} R)) := by
    change PreservesLimits (coyoneda.obj (op P))
    infer_instance
  exact preservesLimits_of_reflects_of_preserves _ (forget (ModuleCat.{u} R))

/-- Projectivity makes linear Hom preserve epimorphisms of coefficients. -/
instance linearCoyonedaModule_preservesEpimorphisms
    (P : ModuleCat.{u} R) [Projective P] :
    ((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)).PreservesEpimorphisms := by
  let : (coyoneda.obj (op P)).PreservesEpimorphisms :=
    (Projective.projective_iff_preservesEpimorphisms_coyoneda_obj P).mp inferInstance
  have : (((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)) ⋙
      forget (ModuleCat.{u} R)).PreservesEpimorphisms := by
    change (coyoneda.obj (op P)).PreservesEpimorphisms
    infer_instance
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects
    ((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)) (forget (ModuleCat.{u} R))

/-- Linear Hom out of a projective module preserves homology of coefficient short complexes. -/
instance linearCoyonedaModule_preservesHomology (P : ModuleCat.{u} R) [Projective P] :
    ((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Linear Hom out of a projective module preserves finite colimits of coefficients. -/
instance linearCoyonedaModule_preservesFiniteColimits
    (P : ModuleCat.{u} R) [Projective P] :
    PreservesFiniteColimits ((linearCoyoneda R (ModuleCat.{u} R)).obj (op P)) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- The entire dual cochain coefficient functor preserves finite limits. -/
instance chainLinearYonedaFunctor_preservesFiniteLimits
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    PreservesFiniteLimits (chainLinearYonedaFunctor K) where
  preservesFiniteLimits J _ _ :=
    preservesLimitsOfShape_of_eval _ (fun i => by
      change PreservesLimitsOfShape J ((linearCoyoneda R (ModuleCat.{u} R)).obj (op (K.X i)))
      infer_instance)

/-- Degreewise projective chain complexes give exact dual cochain coefficient functors. -/
instance chainLinearYonedaFunctor_preservesFiniteColimits
    (K : ChainComplex (ModuleCat.{u} R) ℕ) [∀ i, Projective (K.X i)] :
    PreservesFiniteColimits (chainLinearYonedaFunctor K) where
  preservesFiniteColimits J _ _ :=
    preservesColimitsOfShape_of_eval _ (fun i => by
      change PreservesColimitsOfShape J ((linearCoyoneda R (ModuleCat.{u} R)).obj (op (K.X i)))
      infer_instance)

end SerrePositivity
