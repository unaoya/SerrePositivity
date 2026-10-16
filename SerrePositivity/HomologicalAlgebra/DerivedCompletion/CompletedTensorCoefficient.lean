module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Coefficient
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0AlgebraUniversal

/-! # Original factor multiplication on the actual completed tensor H⁰ ring -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The original left coefficient acts through its original completed factor map. -/
def completedTensorH0LeftAlgHom :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
    S →ₐ[R] (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R a S T).X.obj := by
  letI : CommRing ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)) :=
    derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  letI : Algebra R ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)) :=
    derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
  exact (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R a S T)).comp
    (derivedSingleH0AlgEquiv (R := R) S).symm.toAlgHom

/-- The left algebra map retains precisely the original factor and canonical single H⁰ class. -/
lemma completedTensorH0LeftAlgHom_apply (s : S) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
    completedTensorH0LeftAlgHom R a S T s =
      derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R a S T)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R S) s) := by
  letI : CommRing ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)) :=
    derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  letI : Algebra R ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)) :=
    derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
  have he : (derivedSingleH0AlgEquiv (R := R) S).symm s =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R S) s := by
    apply (derivedSingleH0AlgEquiv (R := R) S).injective
    rw [AlgEquiv.apply_symm_apply, derivedSingleH0AlgEquiv_apply]
    exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app
      (ModuleCat.of R S)).toLinearEquiv.apply_symm_apply s |>.symm
  change derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R a S T)
    ((derivedSingleH0AlgEquiv (R := R) S).symm s) = _
  rw [he]

@[instance_reducible] def completedTensorH0LeftAlgebra :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
    Algebra S ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R a S T).X.obj) := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
  exact (completedTensorH0LeftAlgHom R a S T).toRingHom.toAlgebra

/-- The target's original R action agrees with restriction of the original left-coefficient action. -/
lemma completedTensorH0LeftScalarTower :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
    letI := completedTensorH0LeftAlgebra R a S T
    IsScalarTower R S ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R a S T).X.obj) := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
  letI := completedTensorH0LeftAlgebra R a S T
  exact IsScalarTower.of_algHom (completedTensorH0LeftAlgHom R a S T)

/-- The completed original left-coefficient endomorphism acts by multiplication
by the original completed factor image. No flatness or regularity is needed. -/
lemma completedTensorH0_left_coefficient_mul (s : S)
    (z : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R a S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
        (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R s)))
          (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))))).hom z =
      derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R a S T)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R S) s) * z := by
  let A := boundedAboveDerivedTensorAlgebra (R := R) S T
  let AC := (boundedAboveCompletionCommMonFunctor R a).obj A
  let H := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj AC.X.obj
  letI := derivedH0CommRing A
  letI := derivedH0Algebra A
  letI := derivedH0CommRing AC
  letI := derivedH0Algebra AC
  letI : A.X.obj.IsLE 0 := by
    change ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R S)).obj
      (ModuleCat.of R T)).IsLE 0
    infer_instance
  let c : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
      (ModuleCat.of R S) s
  let J : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj →ₐ[R] H :=
    derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a A)
  let b : H := derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R a S T) c
  let f : A.X ⟶ A.X := boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
    (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R s)))
    (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))))
  let l : H →ₗ[R] H := ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    ((boundedAboveDerivedCompletionFunctor R a).map f).hom).hom
  let m : H →ₗ[R] H := LinearMap.mulLeft R b
  have hc : IsModuleComplete R a (ModuleCat.of R H) :=
    derivedComplexCompletionFunctor_homology_isModuleComplete R a A.X.obj 0
  have hb : J (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) c) = b := by
    change derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a A)
      (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) c) = _
    rw [derivedH0AlgMap_comp_apply]
    rfl
  have hJ (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
      l (J x) = b * J x := by
    have hn := congrArg (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      (congrArg (fun h => h.hom) ((boundedAboveDerivedCompletionUnit R a).naturality f))
    simp only [Functor.id_map, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at hn
    have hx := congrArg (fun h => h.hom x) hn
    calc
      l (J x) = J ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom x) := by
        dsimp only [l, J]
        rw [completionH0AlgebraUnit_apply, completionH0AlgebraUnit_apply]
        exact hx.symm
      _ = J (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) c * x) :=
        congrArg J (derivedTensorH0_left_coefficient_mul S T s x)
      _ = b * J x := by rw [map_mul, hb]
  have hcomp : l.comp J.toLinearMap = m.comp J.toLinearMap := by
    ext x
    exact hJ x
  have he : l = m := (completionH0_linear_ext R a A H hc) hcomp
  exact LinearMap.congr_fun he z

/-- The original completed factor endomorphism is exactly the original left algebra scalar action. -/
lemma completedTensorH0_left_coefficient_smul (s : S)
    (z : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R a S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
    letI := completedTensorH0LeftAlgebra R a S T
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
        (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R s)))
          (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))))).hom z = s • z := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
  letI := completedTensorH0LeftAlgebra R a S T
  change _ = completedTensorH0LeftAlgHom R a S T s * z
  rw [completedTensorH0LeftAlgHom_apply]
  exact completedTensorH0_left_coefficient_mul R a S T s z

end SerrePositivity.DerivedCompletion
