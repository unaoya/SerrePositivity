module
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionDerivedComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionPointAction

/-! # Compare completion of a discrete algebra over the base and over itself -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R) (B : Type u) [CommRing B] [Algebra R B]

/-- The actual discrete algebra completed over the original base ring. -/
abbrev completedAlgebra :=
  (boundedAboveCompletionCommMonFunctor R a).obj (boundedAboveDerivedAlgebra (R := R) B)

/-- Complete the original R-algebra module, or complete over B and restrict its coefficients. -/
def completedAlgebraRestrictionIso :
    (completedAlgebra R a B).X.obj ≅
      (derivedRestrictScalars (algebraMap R B)).obj
        (completedUnitAlgebra B (algebraMap R B a)).X.obj :=
  (derivedComplexCompletionFunctor R a).mapIso (algebraRestrictionSingleIso R B).symm ≪≫
    (derivedCompletionRestrictionIso (algebraMap R B) a).app
      ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B B))

/-- The derived comparison preserves the original standard completion unit. -/
lemma completedAlgebraRestrictionIso_unit :
    (derivedComplexCompletionUnit R a).app
        ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R B)) ≫
      (completedAlgebraRestrictionIso R a B).hom =
    (algebraRestrictionSingleIso R B).inv ≫
      (derivedRestrictScalars (algebraMap R B)).map
        ((derivedComplexCompletionUnit B (algebraMap R B a)).app
          ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B B))) := by
  simp only [completedAlgebraRestrictionIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  have hn := (derivedComplexCompletionUnit R a).naturality (algebraRestrictionSingleIso R B).inv
  simp only [CategoryTheory.Functor.id_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc]
  erw [derivedCompletionRestrictionIso_unit]

/-- The comparison respects the completed original multiplication by every coefficient. -/
lemma completedAlgebraRestrictionIso_mul (b : B) :
    (derivedComplexCompletionFunctor R a).map
        ((DerivedCategory.singleFunctor (ModuleCat R) 0).map
          (ModuleCat.ofHom (LinearMap.mulLeft R b))) ≫
      (completedAlgebraRestrictionIso R a B).hom =
    (completedAlgebraRestrictionIso R a B).hom ≫
      (derivedRestrictScalars (algebraMap R B)).map
        ((derivedComplexCompletionFunctor B (algebraMap R B a)).map
          ((DerivedCategory.singleFunctor (ModuleCat B) 0).map
            (ModuleCat.ofHom (LinearMap.mulLeft B b)))) := by
  have h := congrArg (fun f ↦ (algebraRestrictionSingleIso R B).inv ≫ f ≫
    (algebraRestrictionSingleIso R B).inv) (algebraRestrictionSingleIso_mul R B b)
  have hi : (DerivedCategory.singleFunctor (ModuleCat R) 0).map
        (ModuleCat.ofHom (LinearMap.mulLeft R b)) ≫ (algebraRestrictionSingleIso R B).inv =
      (algebraRestrictionSingleIso R B).inv ≫
        (derivedRestrictScalars (algebraMap R B)).map
          ((DerivedCategory.singleFunctor (ModuleCat B) 0).map
            (ModuleCat.ofHom (LinearMap.mulLeft B b))) := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h.symm
  have hiF := congrArg (derivedComplexCompletionFunctor R a).map hi
  simp only [CategoryTheory.Functor.map_comp] at hiF
  have hn := (derivedCompletionRestrictionIso (algebraMap R B) a).hom.naturality
    ((DerivedCategory.singleFunctor (ModuleCat B) 0).map (ModuleCat.ofHom (LinearMap.mulLeft B b)))
  simp only [CategoryTheory.Functor.comp_map] at hn
  simp only [completedAlgebraRestrictionIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  erw [reassoc_of% hiF, hn]
  rfl

/-- The actual H⁰ modules compare by the original G8 and homology restriction isomorphisms. -/
def completedAlgebraRestrictionH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (completedAlgebra R a B).X.obj ≅
      (ModuleCat.restrictScalars (algebraMap R B)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
          (completedUnitAlgebra B (algebraMap R B a)).X.obj) :=
  (DerivedCategory.homologyFunctor (ModuleCat R) 0).mapIso (completedAlgebraRestrictionIso R a B) ≪≫
    (derivedRestrictScalarsHomologyIso (algebraMap R B) 0).app
      (completedUnitAlgebra B (algebraMap R B a)).X.obj

/-- The H⁰ comparison preserves the actual completed coefficient endomorphisms. -/
lemma completedAlgebraRestrictionH0Iso_mul (b : B) :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((derivedComplexCompletionFunctor R a).map
          ((DerivedCategory.singleFunctor (ModuleCat R) 0).map
            (ModuleCat.ofHom (LinearMap.mulLeft R b)))) ≫
      (completedAlgebraRestrictionH0Iso R a B).hom =
    (completedAlgebraRestrictionH0Iso R a B).hom ≫
      (ModuleCat.restrictScalars (algebraMap R B)).map
        ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map
          ((derivedComplexCompletionFunctor B (algebraMap R B a)).map
            ((DerivedCategory.singleFunctor (ModuleCat B) 0).map
              (ModuleCat.ofHom (LinearMap.mulLeft B b))))) := by
  have hd := congrArg (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    (completedAlgebraRestrictionIso_mul R a B b)
  simp only [CategoryTheory.Functor.map_comp] at hd
  have hn := (derivedRestrictScalarsHomologyIso (algebraMap R B) 0).hom.naturality
    ((derivedComplexCompletionFunctor B (algebraMap R B a)).map
      ((DerivedCategory.singleFunctor (ModuleCat B) 0).map
        (ModuleCat.ofHom (LinearMap.mulLeft B b))))
  simp only [CategoryTheory.Functor.comp_map] at hn
  simp only [completedAlgebraRestrictionH0Iso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  erw [reassoc_of% hd, hn]
  rfl

/-- Multiplication by the standard image of b becomes its original B-scalar action. -/
lemma completedAlgebraRestrictionH0Iso_coefficient (b : B)
    (y : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (completedAlgebra R a B).X.obj) :
    letI := derivedH0CommRing (completedAlgebra R a B)
    (completedAlgebraRestrictionH0Iso R a B).hom
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) B))
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R B) b) * y) =
      (fun z : (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
          (completedUnitAlgebra B (algebraMap R B a)).X.obj ↦ b • z)
        ((completedAlgebraRestrictionH0Iso R a B).hom y) := by
  let := derivedH0CommRing (completedAlgebra R a B)
  have h := congrArg (fun f ↦ f.hom y) (completedAlgebraRestrictionH0Iso_mul R a B b)
  change (completedAlgebraRestrictionH0Iso R a B).hom
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((boundedAboveDerivedCompletionFunctor R a).map
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R b)))).hom y) =
    (DerivedCategory.homologyFunctor (ModuleCat B) 0).map
      ((boundedAboveDerivedCompletionFunctor B (algebraMap R B a)).map
        (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft B b)))).hom
      ((completedAlgebraRestrictionH0Iso R a B).hom y) at h
  rw [boundedAboveCompletion_discrete_mul_homology,
    boundedAboveCompletion_coefficient_smul_homology] at h
  exact h

end SerrePositivity.DerivedCompletion
