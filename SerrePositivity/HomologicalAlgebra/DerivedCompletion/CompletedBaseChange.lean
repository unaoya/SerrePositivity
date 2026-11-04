module

public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeScalar
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion
public import SerrePositivity.HomologicalAlgebra.DerivedHomologyLinear
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Coefficient
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.HomologicalAlgebra.AlgebraBaseChangeTensorH0

/-! # 完備導来基底変更の係数

## 概要

完備導来基底変更の後の目標のスカラーの作用（`completedBaseChangeTensorRestrictionIso`）、完備テンソルの H⁰ 環の上の元の因子の乗法（`completedTensorH0LeftAlgHom`）、新しい基底の上の H⁰ 加群と完備テンソルの係数代数（`completedBaseChangeTensorH0Iso`）、実際の完備基底変更と元の導来テンソルの標準単位の一致を与える。

## 方針

元の導来テンソルの単位で比べ、H⁰ では係数の作用を保つ。

## 規約

旧 `CompletedBaseChangeScalar`・`CompletedTensorCoefficient`・`CompletedBaseChangeH0Coefficient`・`AlgebraBaseChangeTensorUnit`。

## 使われ方

`CompletedAlgebraH0`、BhattScholze。
-/

@[expose] public noncomputable section

universe u

section CompletedBaseChangeScalarPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard

/-- The actual completion preserves scalar identity maps by uniqueness along its original unit. -/
lemma derivedCompletion_map_scalar_id (R : Type u) [CommRing R] (a : R)
    (X : ConcreteDerivedCategory R) (s : R) :
    (derivedComplexCompletionFunctor R a).map (s • 𝟙 X) =
      s • 𝟙 ((derivedComplexCompletionFunctor R a).obj X) := by
  apply derivedComplexCompletionHom_ext R a
    (derivedComplexCompletionFunctor_isComplete R a X)
  calc
    (derivedComplexCompletionUnit R a).app X ≫
        (derivedComplexCompletionFunctor R a).map (s • 𝟙 X) =
      (s • 𝟙 X) ≫ (derivedComplexCompletionUnit R a).app X :=
      ((derivedComplexCompletionUnit R a).naturality (s • 𝟙 X)).symm
    _ = s • (derivedComplexCompletionUnit R a).app X := by simp
    _ = (derivedComplexCompletionUnit R a).app X ≫
      (s • 𝟙 ((derivedComplexCompletionFunctor R a).obj X)) := by simp

lemma boundedAboveCompletion_map_scalar_id (R : Type u) [CommRing R] (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (s : R) :
    (boundedAboveDerivedCompletionFunctor R a).map (s • 𝟙 X) =
      s • 𝟙 ((boundedAboveDerivedCompletionFunctor R a).obj X) := by
  apply InducedCategory.hom_ext
  exact derivedCompletion_map_scalar_id R a X.obj s

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (a : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- Complete the original S-base change and restrict, or complete its original R-tensor model. -/
def completedBaseChangeTensorRestrictionIso (X : D) :
    (boundedAboveDerivedRestrictScalars φ).obj
        ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
          ((boundedAboveDerivedBaseChange φ).obj X)) ≅
      (boundedAboveDerivedCompletionFunctor R a).obj
        (boundedAboveDerivedTensor.obj (derivedBaseChangeScalarObject φ, X)) :=
  ((boundedAboveCompletionRestrictionIso φ a).app
    ((boundedAboveDerivedBaseChange φ).obj X)).symm ≪≫
      (boundedAboveDerivedCompletionFunctor R a).mapIso
        (boundedAboveDerivedBaseChangeTensorIso φ X)

/-- Every original S scalar becomes its completed original scalar-factor multiplication. -/
lemma completedBaseChangeTensorRestrictionIso_scalar (X : D) (s : S) :
    (boundedAboveDerivedRestrictScalars φ).map
        (s • 𝟙 ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
          ((boundedAboveDerivedBaseChange φ).obj X))) ≫
        (completedBaseChangeTensorRestrictionIso φ a X).hom =
      (completedBaseChangeTensorRestrictionIso φ a X).hom ≫
        (boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
          (CategoryTheory.Prod.mkHom
            (show derivedBaseChangeScalarObject φ ⟶ derivedBaseChangeScalarObject φ from
              boundedAboveDerivedSingleFunctor.map (restrictedScalarMultiplication φ s)) (𝟙 X))) := by
  have hn := (boundedAboveCompletionRestrictionIso φ a).inv.naturality
    (s • 𝟙 ((boundedAboveDerivedBaseChange φ).obj X))
  simp only [Functor.comp_map] at hn
  rw [boundedAboveCompletion_map_scalar_id] at hn
  change (boundedAboveDerivedRestrictScalars φ).map
      (s • 𝟙 ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
        ((boundedAboveDerivedBaseChange φ).obj X))) ≫
      ((boundedAboveCompletionRestrictionIso φ a).app
        ((boundedAboveDerivedBaseChange φ).obj X)).inv =
    ((boundedAboveCompletionRestrictionIso φ a).app
      ((boundedAboveDerivedBaseChange φ).obj X)).inv ≫
      (boundedAboveDerivedCompletionFunctor R a).map
        ((boundedAboveDerivedRestrictScalars φ).map
          (s • 𝟙 ((boundedAboveDerivedBaseChange φ).obj X))) at hn
  simp only [completedBaseChangeTensorRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, hn, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (boundedAboveDerivedCompletionFunctor R a).map
    (boundedAboveDerivedBaseChangeTensorIso_scalar φ X s)

/-- The actual homology comparison retains the original S module on its source. -/
def completedBaseChangeTensorRestrictionHomologyIso (X : D) (i : ℤ) :
    (ModuleCat.restrictScalars φ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj
          ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
            ((boundedAboveDerivedBaseChange φ).obj X)).obj) ≅
      (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        ((boundedAboveDerivedCompletionFunctor R a).obj
          (boundedAboveDerivedTensor.obj (derivedBaseChangeScalarObject φ, X))).obj :=
  ((derivedRestrictScalarsHomologyIso φ i).app
    ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj X)).obj).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      (DerivedCategory.Minus.ι.mapIso (completedBaseChangeTensorRestrictionIso φ a X))

/-- At every actual homology degree the comparison intertwines every target scalar
with the original completed scalar-factor action. -/
lemma completedBaseChangeTensorRestrictionHomologyIso_scalar (X : D) (i : ℤ) (s : S)
    (x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
      ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
        ((boundedAboveDerivedBaseChange φ).obj X)).obj) :
    (completedBaseChangeTensorRestrictionHomologyIso φ a X i).hom (s • x) =
      (DerivedCategory.homologyFunctor (ModuleCat R) i).map
        ((boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
          (CategoryTheory.Prod.mkHom
            (show derivedBaseChangeScalarObject φ ⟶ derivedBaseChangeScalarObject φ from
              boundedAboveDerivedSingleFunctor.map (restrictedScalarMultiplication φ s)) (𝟙 X)))).hom
        ((completedBaseChangeTensorRestrictionHomologyIso φ a X i).hom x) := by
  let Y := (boundedAboveDerivedCompletionFunctor S (φ a)).obj
    ((boundedAboveDerivedBaseChange φ).obj X)
  have hd := congrArg (DerivedCategory.homologyFunctor (ModuleCat R) i).map
    (congrArg (fun f => f.hom) (completedBaseChangeTensorRestrictionIso_scalar φ a X s))
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at hd
  have hn := (derivedRestrictScalarsHomologyIso φ i).inv.naturality (s • 𝟙 Y.obj)
  simp only [Functor.comp_map] at hn
  change (ModuleCat.restrictScalars φ).map
      ((DerivedCategory.homologyFunctor (ModuleCat S) i).map (s • 𝟙 Y.obj)) ≫
      ((derivedRestrictScalarsHomologyIso φ i).app Y.obj).inv =
    ((derivedRestrictScalarsHomologyIso φ i).app Y.obj).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) i).map
        ((derivedRestrictScalars φ).map (s • 𝟙 Y.obj)) at hn
  dsimp only [Y] at hn
  have ht : (ModuleCat.restrictScalars φ).map
      ((DerivedCategory.homologyFunctor (ModuleCat S) i).map (s • 𝟙 Y.obj)) ≫
      (completedBaseChangeTensorRestrictionHomologyIso φ a X i).hom =
    (completedBaseChangeTensorRestrictionHomologyIso φ a X i).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) i).map
        ((boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
          (CategoryTheory.Prod.mkHom
            (show derivedBaseChangeScalarObject φ ⟶ derivedBaseChangeScalarObject φ from
              boundedAboveDerivedSingleFunctor.map (restrictedScalarMultiplication φ s)) (𝟙 X)))).hom := by
    simp only [completedBaseChangeTensorRestrictionHomologyIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Category.assoc]
    rw [← Category.assoc, hn, Category.assoc]
    congr 1
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id] at ht
  exact congrArg (fun f => f.hom x) ht

end SerrePositivity.DerivedCompletion

end CompletedBaseChangeScalarPart

section CompletedTensorCoefficientPart

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

end CompletedTensorCoefficientPart

section CompletedBaseChangeH0CoefficientPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]

/-- Normalize the original restricted scalar factor without changing its elements. -/
def baseChangeScalarNormalizationIso :
    derivedBaseChangeScalarObject (algebraMap R S) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S) :=
  boundedAboveDerivedSingleFunctor.mapIso (algebraSelfRestrictionIso R S)

lemma baseChangeScalarNormalizationIso_scalar (s : S) :
    (show derivedBaseChangeScalarObject (algebraMap R S) ⟶
      derivedBaseChangeScalarObject (algebraMap R S) from
      boundedAboveDerivedSingleFunctor.map (restrictedScalarMultiplication (algebraMap R S) s)) ≫
        (baseChangeScalarNormalizationIso R S).hom =
      (baseChangeScalarNormalizationIso R S).hom ≫
        boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R s)) := by
  have h : restrictedScalarMultiplication (algebraMap R S) s ≫
      (algebraSelfRestrictionIso R S).hom =
    (algebraSelfRestrictionIso R S).hom ≫ ModuleCat.ofHom (LinearMap.mulLeft R s) := by
    ext x
    rfl
  change boundedAboveDerivedSingleFunctor.map _ ≫ boundedAboveDerivedSingleFunctor.map _ =
    boundedAboveDerivedSingleFunctor.map _ ≫ boundedAboveDerivedSingleFunctor.map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h]

variable (a : R)

/-- The actual tensor normalization retains the original scalar factor. -/
def completedScalarTensorNormalizationIso :
    (boundedAboveDerivedCompletionFunctor R a).obj
        (boundedAboveDerivedTensor.obj
          (derivedBaseChangeScalarObject (algebraMap R S),
            boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))) ≅
      (boundedAboveCompletedTensorAlgebra R a S T).X :=
  (boundedAboveDerivedCompletionFunctor R a).mapIso
    (boundedAboveDerivedTensor.mapIso
      (Iso.prod (baseChangeScalarNormalizationIso R S)
        (Iso.refl (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))))

lemma completedScalarTensorNormalizationIso_scalar (s : S) :
    (boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
      (CategoryTheory.Prod.mkHom
        (show derivedBaseChangeScalarObject (algebraMap R S) ⟶
          derivedBaseChangeScalarObject (algebraMap R S) from
          boundedAboveDerivedSingleFunctor.map
            (restrictedScalarMultiplication (algebraMap R S) s))
        (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))))) ≫
      (completedScalarTensorNormalizationIso R S T a).hom =
    (completedScalarTensorNormalizationIso R S T a).hom ≫
      (boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
        (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R s)))
          (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))))) := by
  simp only [completedScalarTensorNormalizationIso, Functor.mapIso_hom, Iso.prod_hom,
    Iso.refl_hom]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  congr 1
  apply CategoryTheory.Prod.hom_ext
  · exact baseChangeScalarNormalizationIso_scalar R S s
  · simp

/-- Original S-homology, after restriction, compared to the original completed tensor H⁰. -/
def completedBaseChangeTensorH0Iso :
    (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
          ((boundedAboveDerivedCompletionFunctor S (algebraMap R S a)).obj
            ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
              (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))).obj) ≅
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveCompletedTensorAlgebra R a S T).X.obj :=
  completedBaseChangeTensorRestrictionHomologyIso (algebraMap R S) a
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)) 0 ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (completedScalarTensorNormalizationIso R S T a))

/-- Every original S-scalar is preserved, for the original left-factor algebra action. -/
lemma completedBaseChangeTensorH0Iso_smul (s : S)
    (x : (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
      ((boundedAboveDerivedCompletionFunctor S (algebraMap R S a)).obj
        ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))).obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
    letI := completedTensorH0LeftAlgebra R a S T
    (completedBaseChangeTensorH0Iso R S T a).hom (s • x) =
      s • (completedBaseChangeTensorH0Iso R S T a).hom x := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
  letI := completedTensorH0LeftAlgebra R a S T
  have hn := congrArg (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    (congrArg (fun f => f.hom) (completedScalarTensorNormalizationIso_scalar R S T a s))
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at hn
  have hx := completedBaseChangeTensorRestrictionHomologyIso_scalar (algebraMap R S) a
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)) 0 s x
  simp only [completedBaseChangeTensorH0Iso, Iso.trans_hom, Functor.mapIso_hom,
    ModuleCat.comp_apply]
  change _ = s • _
  rw [hx]
  have hp := congrArg (fun f => f.hom
    ((completedBaseChangeTensorRestrictionHomologyIso (algebraMap R S) a
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)) 0).hom x)) hn
  exact hp.trans (completedTensorH0_left_coefficient_smul R a S T s _)

/-- The comparison is S-linear for the original source and original factor algebra target. -/
def completedBaseChangeTensorH0LinearEquiv :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
    letI := completedTensorH0LeftAlgebra R a S T
    (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
      ((boundedAboveDerivedCompletionFunctor S (algebraMap R S a)).obj
        ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))).obj ≃ₗ[S]
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R a S T).X.obj := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
  letI := completedTensorH0LeftAlgebra R a S T
  exact { (completedBaseChangeTensorH0Iso R S T a).toLinearEquiv.toAddEquiv with
    map_smul' := completedBaseChangeTensorH0Iso_smul R S T a }

/-- The S-linear equivalence is precisely the original restricted H⁰ comparison. -/
lemma completedBaseChangeTensorH0LinearEquiv_apply
    (x : (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
      ((boundedAboveDerivedCompletionFunctor S (algebraMap R S a)).obj
        ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))).obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
    letI := completedTensorH0LeftAlgebra R a S T
    completedBaseChangeTensorH0LinearEquiv R S T a x =
      (completedBaseChangeTensorH0Iso R S T a).hom x := rfl

end SerrePositivity.DerivedCompletion

end CompletedBaseChangeH0CoefficientPart

section AlgebraBaseChangeTensorUnitPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R B S : Type u) [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] (a : R)

/-- 元の実完備底変換を係数制限し、正規化した実完備 tensor へ比較する。 -/
def completedAlgebraBaseChangeTensorIso :
    (derivedRestrictScalars (algebraMap R B)).obj
      ((derivedComplexCompletionFunctor B (algebraMap R B a)).obj
        ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) ≅
      (boundedAboveCompletedTensorAlgebra R a B S).X.obj :=
  ((derivedCompletionRestrictionIso (algebraMap R B) a).app _).symm ≪≫
    (derivedComplexCompletionFunctor R a).mapIso (algebraDerivedBaseChangeTensorIso R B S)

/-- 新しい対象を選ばず、既存の係数正規化を含む G2 の比較そのものに等しい。 -/
theorem completedAlgebraBaseChangeTensorIso_eq :
    completedAlgebraBaseChangeTensorIso R B S a =
      DerivedCategory.Minus.ι.mapIso
        (completedBaseChangeTensorRestrictionIso (algebraMap R B) a
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))) ≪≫
      DerivedCategory.Minus.ι.mapIso (completedScalarTensorNormalizationIso R B S a) := by
  apply Iso.ext
  simp only [completedAlgebraBaseChangeTensorIso, completedBaseChangeTensorRestrictionIso,
    completedScalarTensorNormalizationIso, algebraDerivedBaseChangeTensorIso,
    baseChangeScalarNormalizationIso, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  rfl

/-- 完備底変換の元の単位は、比較を通して元の tensor 完備化単位になる。 -/
theorem completedAlgebraBaseChangeTensorIso_unit :
    (derivedRestrictScalars (algebraMap R B)).map
        ((derivedComplexCompletionUnit B (algebraMap R B a)).app
          ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) ≫
      (completedAlgebraBaseChangeTensorIso R B S a).hom =
    (algebraDerivedBaseChangeTensorIso R B S).hom ≫
      (derivedComplexCompletionUnit R a).app
        (boundedAboveDerivedTensorAlgebra (R := R) B S).X.obj := by
  change _ ≫ ((derivedCompletionRestrictionIso (algebraMap R B) a).inv.app _ ≫ _) = _
  rw [← Category.assoc, derivedCompletionRestrictionIso_inv_unit]
  exact ((derivedComplexCompletionUnit R a).naturality
    (algebraDerivedBaseChangeTensorIso R B S).hom).symm

/-- 元の G2 の H⁰ 比較は、元の二つの完備化標準単位と可換。 -/
theorem completedBaseChangeTensorH0Iso_unit :
    (ModuleCat.restrictScalars (algebraMap R B)).map
        ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map
          ((derivedComplexCompletionUnit B (algebraMap R B a)).app
            ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
              (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj)) ≫
      (completedBaseChangeTensorH0Iso R B S a).hom =
    (algebraBaseChangeTensorH0Iso R B S).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((derivedComplexCompletionUnit R a).app
          (boundedAboveDerivedTensorAlgebra (R := R) B S).X.obj) := by
  let φ := algebraMap R B
  let H := DerivedCategory.homologyFunctor (ModuleCat R) 0
  let H' := DerivedCategory.homologyFunctor (ModuleCat B) 0
  let U := ModuleCat.restrictScalars φ
  let X := ((boundedAboveDerivedBaseChange φ).obj
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj
  let η := (derivedComplexCompletionUnit B (φ a)).app X
  let ρ := derivedRestrictScalarsHomologyIso φ 0
  have hc : (completedBaseChangeTensorH0Iso R B S a).hom =
      ρ.inv.app ((derivedComplexCompletionFunctor B (φ a)).obj X) ≫
        H.map (completedAlgebraBaseChangeTensorIso R B S a).hom := by
    rw [completedAlgebraBaseChangeTensorIso_eq]
    simp only [completedBaseChangeTensorH0Iso, completedBaseChangeTensorRestrictionHomologyIso,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rfl
  have hn := ρ.inv.naturality η
  change U.map (H'.map η) ≫ ρ.inv.app ((derivedComplexCompletionFunctor B (φ a)).obj X) =
    ρ.inv.app X ≫ H.map ((derivedRestrictScalars φ).map η) at hn
  rw [hc, ← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    completedAlgebraBaseChangeTensorIso_unit, Functor.map_comp, ← Category.assoc]
  rfl

/-- 単位可換式を元の B 上の全ての H⁰ の元で表したもの。 -/
theorem completedBaseChangeTensorH0Iso_unit_apply
    (x : (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) :
    (completedBaseChangeTensorH0Iso R B S a).hom
        ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map
          ((derivedComplexCompletionUnit B (algebraMap R B a)).app
            ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
              (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) x) =
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((derivedComplexCompletionUnit R a).app
          (boundedAboveDerivedTensorAlgebra (R := R) B S).X.obj)
        ((algebraBaseChangeTensorH0Iso R B S).hom x) :=
  congrArg (fun k => k.hom x) (completedBaseChangeTensorH0Iso_unit R B S a)

end SerrePositivity.DerivedCompletion

end AlgebraBaseChangeTensorUnitPart
