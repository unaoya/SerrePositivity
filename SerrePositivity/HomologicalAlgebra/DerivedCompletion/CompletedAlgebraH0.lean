module

public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal
public import Mathlib.Algebra.Algebra.Tower
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionSingleH0
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairZeroCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAugmentationIso
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
public import SerrePositivity.CommutativeAlgebra.TensorProduct.BaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedDiscreteAlgebraMaps
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # 離散な代数の完備化の H⁰

## 概要

離散な代数の基底の上と自身の上の完備化を比べ（`completedAlgebraRestrictionIso`）、係数代数の作用と標準の係数類の保存を示し、任意の基底代数の完備化の H⁰ がその一つの座標の完備化の代数であること（`completedAlgebraPrincipalH0AlgEquiv`）と PD の完備化との比較を与える。すでに完備な座標を二つの座標の H⁰ から外せること、完備化した導来代数の H⁰ が元の H⁰ の一つの座標の完備化であること、完備な標準のテンソルの添加の Koszul 判定、完備テンソルの H⁰ と PD・古典的な完備化・通常のテンソル経由の環としての比較（`completedTensorH0AdicRingEquiv` ほか）、全射な代数の完備化した乗法を与える。

## 方針

比較は一意存在と環の普遍性から作る。

## 規約

`completedTensorH0AdicRingEquiv(_left/_right/_algebraMap)` は BhattScholze が使うので名前を変えない。PD の d = 0 を経由する同型の重複（refactor-plan §3.6.3）は 2b の B で一本化する候補。旧 `CompletedAlgebra{Restriction, ScalarAction, UnitNormalization, PrincipalComparison, PDComparison}`・`CompleteFirstPairComparison`・`CompletionH0PrincipalComparison`・`CompletedTensor{AugmentationCriterion, PDComparison, H0Comparison, ClassicalComparison, H0RingTransport}`・`CompletedSurjectiveAlgebraMul`。

## 使われ方

BhattScholze（完全 prism のテンソル積・Andre）、CLMST。
-/

@[expose] public noncomputable section

universe u

section CompletedAlgebraRestrictionPart

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

end CompletedAlgebraRestrictionPart

section CompletedAlgebraScalarActionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R) (B : Type u) [CommRing B] [Algebra R B]

/-- The original standard completion unit is a map from B into actual completed H⁰. -/
def completedAlgebraUnitAlgHom :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := derivedH0Algebra (completedAlgebra R a B)
    B →ₐ[R] (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (completedAlgebra R a B).X.obj := by
  letI := derivedH0CommRing (completedAlgebra R a B)
  letI := derivedH0Algebra (completedAlgebra R a B)
  letI : CommRing ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R B)) :=
    derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) B)
  letI : Algebra R ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R B)) :=
    derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) B)
  letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) B)
  letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) B)
  exact (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
      (boundedAboveDerivedAlgebra (R := R) B))).comp
    (derivedSingleH0AlgEquiv (R := R) B).symm.toAlgHom

/-- Its function is the original actual completion map on the standard class of b. -/
lemma completedAlgebraUnitAlgHom_apply (b : B) :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := derivedH0Algebra (completedAlgebra R a B)
    completedAlgebraUnitAlgHom R a B b =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) B))
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R B) b) := rfl

/-- Give actual completed H⁰ its coefficient B-algebra action via the original unit. -/
@[instance_reducible] def completedAlgebraScalarAlgebra :
    letI := derivedH0CommRing (completedAlgebra R a B)
    Algebra B ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (completedAlgebra R a B).X.obj) := by
  letI := derivedH0CommRing (completedAlgebra R a B)
  letI := derivedH0Algebra (completedAlgebra R a B)
  exact (completedAlgebraUnitAlgHom R a B).toRingHom.toAlgebra

/-- The coefficient action forms the original R to B to completed H⁰ scalar tower. -/
lemma completedAlgebraScalarTower :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := derivedH0Algebra (completedAlgebra R a B)
    letI := completedAlgebraScalarAlgebra R a B
    IsScalarTower R B ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (completedAlgebra R a B).X.obj) := by
  let := derivedH0CommRing (completedAlgebra R a B)
  let := derivedH0Algebra (completedAlgebra R a B)
  let := completedAlgebraScalarAlgebra R a B
  exact IsScalarTower.of_algHom (completedAlgebraUnitAlgHom R a B)

/-- The original R-linear G8 H⁰ comparison is linear for the actual coefficient B action. -/
def completedAlgebraRestrictionH0BLinearEquiv :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := completedAlgebraScalarAlgebra R a B
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (completedAlgebra R a B).X.obj ≃ₗ[B]
      (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
        (completedUnitAlgebra B (algebraMap R B a)).X.obj := by
  letI := derivedH0CommRing (completedAlgebra R a B)
  letI := derivedH0Algebra (completedAlgebra R a B)
  letI := completedAlgebraScalarAlgebra R a B
  refine
    { (completedAlgebraRestrictionH0Iso R a B).toLinearEquiv.toEquiv with
      map_add' := (completedAlgebraRestrictionH0Iso R a B).toLinearEquiv.map_add
      map_smul' := ?_ }
  intro b y
  change (completedAlgebraRestrictionH0Iso R a B).hom
    (completedAlgebraUnitAlgHom R a B b * y) = _
  rw [completedAlgebraUnitAlgHom_apply]
  exact completedAlgebraRestrictionH0Iso_coefficient R a B b y

/-- Actual H⁰ is complete over the coefficient algebra with its original unit action. -/
lemma completedAlgebraH0_isModuleComplete :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := completedAlgebraScalarAlgebra R a B
    IsModuleComplete B (algebraMap R B a)
      (ModuleCat.of B ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (completedAlgebra R a B).X.obj)) := by
  let := derivedH0CommRing (completedAlgebra R a B)
  let := completedAlgebraScalarAlgebra R a B
  exact isModuleComplete_of_linearEquiv B (algebraMap R B a) _ _
    (completedAlgebraRestrictionH0BLinearEquiv R a B).symm
    (derivedComplexCompletionFunctor_homology_isModuleComplete B (algebraMap R B a)
      ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B B)) 0)

end SerrePositivity.DerivedCompletion

end CompletedAlgebraScalarActionPart

section CompletedAlgebraUnitNormalizationPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The original R-algebra single comparison is normalized on its actual H⁰. -/
lemma algebraRestrictionSingleIso_homology :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        (algebraRestrictionSingleIso R B).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        (ModuleCat.of R B) =
    (derivedRestrictScalarsHomologyIso (algebraMap R B) 0).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B B)) ≫
      (ModuleCat.restrictScalars (algebraMap R B)).map
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).hom.app
          (ModuleCat.of B B)) ≫ (algebraSelfRestrictionIso R B).hom := by
  simp only [algebraRestrictionSingleIso, Iso.trans_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.naturality
    (algebraSelfRestrictionIso R B).hom
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] at hn
  rw [hn, ← Category.assoc]
  erw [derivedRestrictionSingleH0_normalization]
  rfl

/-- The inverse comparison sends each original standard R class to its original B class. -/
lemma algebraRestrictionSingleIso_inv_homology :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R B) ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        (algebraRestrictionSingleIso R B).inv ≫
      (derivedRestrictScalarsHomologyIso (algebraMap R B) 0).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B B)) =
    (algebraSelfRestrictionIso R B).inv ≫
      (ModuleCat.restrictScalars (algebraMap R B)).map
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).inv.app
          (ModuleCat.of B B)) := by
  have h := congrArg (fun f ↦
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R B) ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        (algebraRestrictionSingleIso R B).inv ≫ f ≫
      (algebraSelfRestrictionIso R B).inv ≫
      (ModuleCat.restrictScalars (algebraMap R B)).map
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).inv.app
          (ModuleCat.of B B))) (algebraRestrictionSingleIso_homology R B)
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_app] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h.symm

namespace DerivedCompletion
variable (a : R)

/-- The actual completed H⁰ comparison preserves the original maps from the coefficient module. -/
lemma completedAlgebraRestrictionH0Iso_unit_map :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R B) ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((derivedComplexCompletionUnit R a).app
          ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R B))) ≫
      (completedAlgebraRestrictionH0Iso R a B).hom =
    (algebraSelfRestrictionIso R B).inv ≫
      (ModuleCat.restrictScalars (algebraMap R B)).map
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).inv.app
          (ModuleCat.of B B) ≫
        (DerivedCategory.homologyFunctor (ModuleCat B) 0).map
          ((derivedComplexCompletionUnit B (algebraMap R B a)).app
            ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B B)))) := by
  simp only [completedAlgebraRestrictionH0Iso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← CategoryTheory.Functor.map_comp_assoc, completedAlgebraRestrictionIso_unit,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (derivedRestrictScalarsHomologyIso (algebraMap R B) 0).hom.naturality
    ((derivedComplexCompletionUnit B (algebraMap R B a)).app
      ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B B)))
  simp only [CategoryTheory.Functor.comp_map] at hn
  erw [hn, ← Category.assoc, ← Category.assoc, algebraRestrictionSingleIso_inv_homology]
  rw [Category.assoc, CategoryTheory.Functor.map_comp]

/-- Every standard coefficient class is preserved by the actual completed comparison. -/
lemma completedAlgebraRestrictionH0Iso_unit (b : B) :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := derivedH0Algebra (completedAlgebra R a B)
    letI := derivedH0CommRing (completedUnitAlgebra B (algebraMap R B a))
    letI := derivedH0Algebra (completedUnitAlgebra B (algebraMap R B a))
    (completedAlgebraRestrictionH0Iso R a B).hom (completedAlgebraUnitAlgHom R a B b) =
      completedAlgebraUnitAlgHom B (algebraMap R B a) B b := by
  let := derivedH0CommRing (completedAlgebra R a B)
  let := derivedH0Algebra (completedAlgebra R a B)
  let := derivedH0CommRing (completedUnitAlgebra B (algebraMap R B a))
  let := derivedH0Algebra (completedUnitAlgebra B (algebraMap R B a))
  rw [completedAlgebraUnitAlgHom_apply, completedAlgebraUnitAlgHom_apply,
    completionH0AlgebraUnit_apply, completionH0AlgebraUnit_apply]
  exact congrArg (fun f ↦ f.hom b) (completedAlgebraRestrictionH0Iso_unit_map R B a)

/-- In particular the original comparison carries the actual H⁰ ring unit to the actual unit. -/
lemma completedAlgebraRestrictionH0Iso_one :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := derivedH0CommRing (completedUnitAlgebra B (algebraMap R B a))
    (completedAlgebraRestrictionH0Iso R a B).hom 1 =
      (1 : (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
        (completedUnitAlgebra B (algebraMap R B a)).X.obj) := by
  let := derivedH0CommRing (completedAlgebra R a B)
  let := derivedH0Algebra (completedAlgebra R a B)
  let := derivedH0CommRing (completedUnitAlgebra B (algebraMap R B a))
  let := derivedH0Algebra (completedUnitAlgebra B (algebraMap R B a))
  simpa only [map_one] using completedAlgebraRestrictionH0Iso_unit R B a 1

end DerivedCompletion
end SerrePositivity

end CompletedAlgebraUnitNormalizationPart

section CompletedAlgebraPrincipalComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R) (B : Type u) [CommRing B] [Algebra R B]

/-- Upgrade the original coefficient comparison using the principal module reflection. -/
def completedAlgebraPrincipalH0AlgEquiv :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := completedAlgebraScalarAlgebra R a B
    letI := principalCompletionCommRing B (algebraMap R B a)
    letI := principalCompletionAlgebra B (algebraMap R B a)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (completedAlgebra R a B).X.obj ≃ₐ[B]
      PrincipalCompletionH0 B (algebraMap R B a) := by
  letI := derivedH0CommRing (completedAlgebra R a B)
  letI := completedAlgebraScalarAlgebra R a B
  letI := derivedH0CommRing (completedUnitAlgebra B (algebraMap R B a))
  letI := derivedH0Algebra (completedUnitAlgebra B (algebraMap R B a))
  letI := principalCompletionCommRing B (algebraMap R B a)
  letI := principalCompletionAlgebra B (algebraMap R B a)
  let E := (completedAlgebraRestrictionH0BLinearEquiv R a B).trans
    (principalCompletedUnitH0AlgEquiv B (algebraMap R B a)).toLinearEquiv
  let h := principalCompletionH0_isCompleteModuleReflection B (algebraMap R B a)
  have hT : ∀ _j : Fin 1, IsModuleComplete B (algebraMap R B a)
      (ModuleCat.of B ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (completedAlgebra R a B).X.obj)) := fun _ ↦ completedAlgebraH0_isModuleComplete R a B
  have h1 : E.symm (koszulCompletionH0Unit B (fun _ : Fin 1 ↦ algebraMap R B a) 1) = 1 := by
    apply E.injective
    rw [LinearEquiv.apply_symm_apply]
    change _ = (principalCompletedUnitH0AlgEquiv B (algebraMap R B a))
      ((completedAlgebraRestrictionH0Iso R a B).hom 1)
    rw [completedAlgebraRestrictionH0Iso_one]
    exact (principalCompletedUnitH0Iso_one B (algebraMap R B a)).symm
  exact (AlgEquiv.ofLinearEquiv E.symm h1
    (h.linearMap_map_mul _ hT E.symm.toLinearMap h1)).symm

end SerrePositivity.DerivedCompletion

end CompletedAlgebraPrincipalComparisonPart

section CompletedAlgebraPDComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The original F3 algebra of B, regarded over its original base R. -/
@[instance_reducible] def pdCompletionBaseAlgebra (p : ℕ) (d : B) :
    letI := pdCompletionCommRing B p d
    Algebra R (PDCompletionH0 B p d) := by
  letI := pdCompletionCommRing B p d
  exact ((pdCompletionUnit B p d).comp (algebraMap R B)).toAlgebra

/-- This coefficient restriction has the original R to B to F3 scalar tower. -/
lemma pdCompletionBaseScalarTower (p : ℕ) (d : B) :
    letI := pdCompletionCommRing B p d
    letI := pdCompletionAlgebra B p d
    letI := pdCompletionBaseAlgebra R B p d
    IsScalarTower R B (PDCompletionH0 B p d) := by
  let := pdCompletionCommRing B p d
  let := pdCompletionAlgebra B p d
  let := pdCompletionBaseAlgebra R B p d
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- Completing B over R gives the original F3 (p,0) algebra, with its B-algebra structure. -/
def completedAlgebraH0PDBAlgEquiv (p : ℕ) :
    letI := derivedH0CommRing (completedAlgebra R (p : R) B)
    letI := completedAlgebraScalarAlgebra R (p : R) B
    letI := pdCompletionCommRing B p 0
    letI := pdCompletionAlgebra B p 0
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (completedAlgebra R (p : R) B).X.obj ≃ₐ[B] PDCompletionH0 B p 0 := by
  letI := derivedH0CommRing (completedAlgebra R (p : R) B)
  letI := completedAlgebraScalarAlgebra R (p : R) B
  letI := pdCompletionCommRing B p 0
  letI := pdCompletionAlgebra B p 0
  letI := principalCompletionCommRing B (p : B)
  letI := principalCompletionAlgebra B (p : B)
  have aux (c : B) (hc : algebraMap R B (p : R) = c) :
      letI := principalCompletionCommRing B c
      letI := principalCompletionAlgebra B c
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (completedAlgebra R (p : R) B).X.obj ≃ₐ[B] PrincipalCompletionH0 B c := by
    subst c
    exact completedAlgebraPrincipalH0AlgEquiv R (p : R) B
  let e := aux (p : B) (map_natCast (algebraMap R B) p)
  exact e.trans (pairCompletionZeroPrincipalAlgEquiv B (p : B)).symm

/-- The comparison is an R-algebra equivalence for the original actual H⁰ algebra structure. -/
def completedAlgebraH0PDAlgEquiv (p : ℕ) :
    letI := derivedH0CommRing (completedAlgebra R (p : R) B)
    letI := derivedH0Algebra (completedAlgebra R (p : R) B)
    letI := pdCompletionCommRing B p 0
    letI := pdCompletionBaseAlgebra R B p 0
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (completedAlgebra R (p : R) B).X.obj ≃ₐ[R] PDCompletionH0 B p 0 := by
  letI := derivedH0CommRing (completedAlgebra R (p : R) B)
  letI := derivedH0Algebra (completedAlgebra R (p : R) B)
  letI := completedAlgebraScalarAlgebra R (p : R) B
  letI := completedAlgebraScalarTower R (p : R) B
  letI := pdCompletionCommRing B p 0
  letI := pdCompletionAlgebra B p 0
  letI := pdCompletionBaseAlgebra R B p 0
  letI := pdCompletionBaseScalarTower R B p 0
  exact (completedAlgebraH0PDBAlgEquiv R B p).restrictScalars R

/-- Every coefficient keeps its original image in the F3 comparison. -/
lemma completedAlgebraH0PDAlgEquiv_unit (p : ℕ) (b : B) :
    letI := derivedH0CommRing (completedAlgebra R (p : R) B)
    letI := derivedH0Algebra (completedAlgebra R (p : R) B)
    letI := pdCompletionCommRing B p 0
    letI := pdCompletionBaseAlgebra R B p 0
    completedAlgebraH0PDAlgEquiv R B p (completedAlgebraUnitAlgHom R (p : R) B b) =
      pdCompletionUnit B p 0 b := by
  let := derivedH0CommRing (completedAlgebra R (p : R) B)
  let := derivedH0Algebra (completedAlgebra R (p : R) B)
  let := completedAlgebraScalarAlgebra R (p : R) B
  let := pdCompletionCommRing B p 0
  let := pdCompletionAlgebra B p 0
  let := pdCompletionBaseAlgebra R B p 0
  exact (completedAlgebraH0PDBAlgEquiv R B p).commutes b

end SerrePositivity.DerivedCompletion

end CompletedAlgebraPDComparisonPart

section CompleteFirstPairComparisonPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type u) [CommRing R] (a b : R)
    (hc : IsModuleComplete R a (ModuleCat.of R R))

include hc in
/-- Principal b-completion preserves the base a-completeness. -/
lemma principalCompletionH0_isModuleComplete_first_of_base :
    IsModuleComplete R a (PrincipalCompletionH0 R b) := by
  exact principalCompletionH0_isModuleComplete_of_other R R a b hc

/-- The actual pair completion maps to the principal completion by its universal property. -/
def pairCompletionToPrincipalOfCompleteFirst :
    letI := pairCompletionCommRing R a b
    letI := pairCompletionAlgebra R a b
    letI := principalCompletionCommRing R b
    letI := principalCompletionAlgebra R b
    PairCompletionH0 R a b →ₐ[R] PrincipalCompletionH0 R b := by
  letI := principalCompletionCommRing R b
  letI := principalCompletionAlgebra R b
  exact pairCompletionLiftAlgHom R a b (PrincipalCompletionH0 R b)
    (principalCompletionH0_isModuleComplete_first_of_base R a b hc)
    (principalCompletionH0_isModuleComplete R b)

/-- The principal completion maps to the actual pair completion. -/
def principalCompletionToPair :
    letI := pairCompletionCommRing R a b
    letI := pairCompletionAlgebra R a b
    letI := principalCompletionCommRing R b
    letI := principalCompletionAlgebra R b
    PrincipalCompletionH0 R b →ₐ[R] PairCompletionH0 R a b := by
  letI := pairCompletionCommRing R a b
  letI := pairCompletionAlgebra R a b
  exact principalCompletionLiftAlgHom R b (PairCompletionH0 R a b)
    (pairCompletionH0_isModuleComplete_second R a b)

/-- The two universal maps compose to the identity on principal H0. -/
lemma pairCompletionToPrincipal_comp :
    letI := pairCompletionCommRing R a b
    letI := pairCompletionAlgebra R a b
    letI := principalCompletionCommRing R b
    letI := principalCompletionAlgebra R b
    (pairCompletionToPrincipalOfCompleteFirst R a b hc).comp (principalCompletionToPair R a b) =
      AlgHom.id R (PrincipalCompletionH0 R b) := by
  let := pairCompletionCommRing R a b
  let := pairCompletionAlgebra R a b
  let := principalCompletionCommRing R b
  let := principalCompletionAlgebra R b
  exact (principalCompletion_existsUnique_algHom R b (PrincipalCompletionH0 R b)
    (principalCompletionH0_isModuleComplete R b)).unique trivial trivial

/-- They also compose to the identity on the actual pair H0. -/
lemma principalCompletionToPair_comp :
    letI := pairCompletionCommRing R a b
    letI := pairCompletionAlgebra R a b
    letI := principalCompletionCommRing R b
    letI := principalCompletionAlgebra R b
    (principalCompletionToPair R a b).comp (pairCompletionToPrincipalOfCompleteFirst R a b hc) =
      AlgHom.id R (PairCompletionH0 R a b) := by
  let := pairCompletionCommRing R a b
  let := pairCompletionAlgebra R a b
  let := principalCompletionCommRing R b
  let := principalCompletionAlgebra R b
  exact (pairCompletion_existsUnique_algHom R a b (PairCompletionH0 R a b)
    (pairCompletionH0_isModuleComplete_first R a b)
    (pairCompletionH0_isModuleComplete_second R a b)).unique trivial trivial

/-- An already complete first coordinate can be removed on actual H0 algebras. -/
def pairCompletionPrincipalAlgEquivOfCompleteFirst :
    letI := pairCompletionCommRing R a b
    letI := pairCompletionAlgebra R a b
    letI := principalCompletionCommRing R b
    letI := principalCompletionAlgebra R b
    PairCompletionH0 R a b ≃ₐ[R] PrincipalCompletionH0 R b := by
  letI := pairCompletionCommRing R a b
  letI := pairCompletionAlgebra R a b
  letI := principalCompletionCommRing R b
  letI := principalCompletionAlgebra R b
  exact AlgEquiv.ofAlgHom (pairCompletionToPrincipalOfCompleteFirst R a b hc)
    (principalCompletionToPair R a b) (pairCompletionToPrincipal_comp R a b hc)
    (principalCompletionToPair_comp R a b hc)

end SerrePositivity.DerivedCompletion

end CompleteFirstPairComparisonPart

section CompletionH0PrincipalComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
set_option quotPrecheck false in
local notation "B" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
  ((boundedAboveCompletionCommMonFunctor R a).obj A).X.obj
local notation "J" => derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a A)
/-- The coefficient H⁰(A) acts through the original H⁰ completion unit. -/
@[instance_reducible] def completionH0ScalarAlgebra :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    Algebra B C := by
  letI := derivedH0CommRing A
  letI := derivedH0Algebra A
  letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  exact (J).toRingHom.toAlgebra

/-- Its R-action is the original actual H⁰ action. -/
lemma completionH0ScalarTower :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := completionH0ScalarAlgebra R a A
    IsScalarTower R B C := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := completionH0ScalarAlgebra R a A
  exact IsScalarTower.of_algHom J

/-- Actual completed H⁰ is complete for the original coefficient image of a. -/
lemma completionH0_isModuleComplete_scalar :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := completionH0ScalarAlgebra R a A
    IsModuleComplete B (algebraMap R B a) (ModuleCat.of B C) := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := completionH0ScalarAlgebra R a A
  let := completionH0ScalarTower R a A
  exact (isModuleComplete_algebraMap_iff R B a C).mpr
    (derivedComplexCompletionFunctor_homology_isModuleComplete R a A.X.obj 0)

variable [A.X.obj.IsLE 0]

/-- Compare actual completed H⁰ with principal completion of its original coefficient ring. -/
def completionH0PrincipalAlgEquiv :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := completionH0ScalarAlgebra R a A
    letI := principalCompletionCommRing B (algebraMap R B a)
    letI := principalCompletionAlgebra B (algebraMap R B a)
    C ≃ₐ[B] PrincipalCompletionH0 B (algebraMap R B a) := by
  letI := derivedH0CommRing A
  letI := derivedH0Algebra A
  letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  letI := completionH0ScalarAlgebra R a A
  letI := completionH0ScalarTower R a A
  let b := algebraMap R B a
  let P := PrincipalCompletionH0 B b
  letI := principalCompletionCommRing B b
  letI := principalCompletionAlgebra B b
  letI : Algebra R P := ((principalCompletionUnitRingHom B b).comp (algebraMap R B)).toAlgebra
  letI : IsScalarTower R B P := IsScalarTower.of_algebraMap_eq' rfl
  have hP : IsModuleComplete R a (ModuleCat.of R P) :=
    (isModuleComplete_algebraMap_iff R B a P).mp (principalCompletionH0_isModuleComplete B b)
  let f0 : B →ₐ[R] P := IsScalarTower.toAlgHom R B P
  let f := completionH0AlgebraLift R a A P hP f0
  have hf := completionH0AlgebraLift_unit R a A P hP f0
  let fB : C →ₐ[B] P :=
    { f.toRingHom with
      commutes' x := by
        change f (J x) = f0 x
        exact congrArg (fun h : B →ₐ[R] P => h x) hf }
  let g := principalCompletionLiftAlgHom B b C
    (completionH0_isModuleComplete_scalar R a A)
  have hfg : fB.comp g = AlgHom.id B P :=
    (principalCompletion_existsUnique_algHom B b P
      (principalCompletionH0_isModuleComplete B b)).unique trivial trivial
  have hc : IsModuleComplete R a (ModuleCat.of R C) :=
    derivedComplexCompletionFunctor_homology_isModuleComplete R a A.X.obj 0
  have hgf : g.comp fB = AlgHom.id B C := by
    apply AlgHom.restrictScalars_injective R
    apply AlgHom.toLinearMap_injective
    apply completionH0_linear_ext R a A C hc
    apply LinearMap.ext
    intro x
    change g (fB (J x)) = J x
    have hfBx := fB.commutes x
    change fB (J x) = algebraMap B P x at hfBx
    rw [hfBx]
    exact g.commutes x
  exact AlgEquiv.ofAlgHom fB g hfg hgf

/-- If the original H⁰ is already c-complete, actual a-completion is its pair completion. -/
def completionH0PairAlgEquivOfCompleteFirst (c : R)
    (hc : IsModuleComplete R c B) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := completionH0ScalarAlgebra R a A
    letI := pairCompletionCommRing B (algebraMap R B c) (algebraMap R B a)
    letI := pairCompletionAlgebra B (algebraMap R B c) (algebraMap R B a)
    C ≃ₐ[B] PairCompletionH0 B (algebraMap R B c) (algebraMap R B a) := by
  letI := derivedH0CommRing A
  letI := derivedH0Algebra A
  letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  letI := completionH0ScalarAlgebra R a A
  letI := pairCompletionCommRing B (algebraMap R B c) (algebraMap R B a)
  letI := pairCompletionAlgebra B (algebraMap R B c) (algebraMap R B a)
  letI := principalCompletionCommRing B (algebraMap R B a)
  letI := principalCompletionAlgebra B (algebraMap R B a)
  have hb : IsModuleComplete B (algebraMap R B c) (ModuleCat.of B B) :=
    (isModuleComplete_algebraMap_iff R B c B).mpr hc
  exact (completionH0PrincipalAlgEquiv R a A).trans
    (pairCompletionPrincipalAlgEquivOfCompleteFirst B (algebraMap R B c)
      (algebraMap R B a) hb).symm

end SerrePositivity.DerivedCompletion

end CompletionH0PrincipalComparisonPart

section CompletedTensorAugmentationCriterionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- Completion inverts the original augmentation exactly when every power-Koszul reduction does. -/
lemma completedTensorAlgebraAugmentation_isIso_iff_koszul
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    IsIso (boundedAboveCompletedTensorAlgebraAugmentation R a S T).hom.hom ↔
      ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R (a ^ n)).map
        (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom) := by
  have he : IsIso (boundedAboveCompletedTensorAlgebraAugmentation R a S T).hom.hom ↔
      IsIso ((derivedComplexCompletionFunctor R a).map
        (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom) := by
    constructor
    · intro h
      have := h
      exact inferInstanceAs (IsIso (DerivedCategory.Minus.ι.map
        (boundedAboveCompletedTensorAlgebraAugmentation R a S T).hom.hom))
    · intro h
      have : IsIso (DerivedCategory.Minus.ι.map
          (boundedAboveCompletedTensorAlgebraAugmentation R a S T).hom.hom) := h
      exact isIso_of_reflects_iso
        (boundedAboveCompletedTensorAlgebraAugmentation R a S T).hom.hom DerivedCategory.Minus.ι
  exact he.trans (boundedAboveCompletion_map_isIso_iff_koszul R a
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom)

end SerrePositivity.DerivedCompletion

end CompletedTensorAugmentationCriterionPart

section CompletedTensorPDComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ)
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The original completed augmentation supplies an F3 algebra comparison whenever invertible. -/
def completedTensorH0PDAlgEquivOfIso
    (h : IsIso (boundedAboveCompletedTensorAlgebraAugmentation R (p : R) S T).hom.hom) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃ₐ[R]
        PDCompletionH0 (S ⊗[R] T) p 0 := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := pdCompletionCommRing (S ⊗[R] T) p 0
  letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  letI := derivedH0CommRing (completedAlgebra R (p : R) (S ⊗[R] T))
  letI := derivedH0Algebra (completedAlgebra R (p : R) (S ⊗[R] T))
  exact (derivedH0AlgEquivOfIsoUnderlying
    (boundedAboveCompletedTensorAlgebraAugmentation R (p : R) S T) h).trans
      (completedAlgebraH0PDAlgEquiv R (S ⊗[R] T) p)

/-- All higher Tor vanishing supplies the original F3 comparison before completion. -/
def completedTensorH0PDAlgEquivOfTor
    (hTor : ∀ n : ℕ, 0 < n →
      IsZero (((Tor (ModuleCat R) n).obj (ModuleCat.of R S)).obj (ModuleCat.of R T))) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃ₐ[R]
        PDCompletionH0 (S ⊗[R] T) p 0 :=
  completedTensorH0PDAlgEquivOfIso R p S T
    (completedTensorAlgebraAugmentation_isIso_of_tor R (p : R) S T hTor)

/-- Alternatively use the exact all-power Koszul criterion after completion. -/
def completedTensorH0PDAlgEquivOfKoszul
    (hKos : ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R ((p : R) ^ n)).map
      (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom)) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃ₐ[R]
        PDCompletionH0 (S ⊗[R] T) p 0 :=
  completedTensorH0PDAlgEquivOfIso R p S T
    ((completedTensorAlgebraAugmentation_isIso_iff_koszul R (p : R) S T).mpr hKos)

end SerrePositivity.DerivedCompletion

end CompletedTensorPDComparisonPart

section CompletedTensorH0ComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Invertibility of the actual H0 map suffices for an H0 algebra equivalence. -/
def derivedH0AlgEquivOfIsoHomology
    {A B : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))} (f : A ⟶ B)
    (hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f.hom.hom.hom)) :
    letI := derivedH0CommRing A
    letI := derivedH0CommRing B
    letI := derivedH0Algebra A
    letI := derivedH0Algebra B
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj ≃ₐ[R]
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj B.X.obj := by
  letI := derivedH0CommRing A
  letI := derivedH0CommRing B
  letI := derivedH0Algebra A
  letI := derivedH0Algebra B
  have := hf
  have hb := ConcreteCategory.bijective_of_isIso
    ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom.hom.hom)
  refine AlgEquiv.ofBijective (derivedH0AlgMap f) ?_
  change Function.Bijective (fun x :
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj ↦
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom.hom.hom x) at hb
  simpa only [← derivedH0AlgMap_apply] using hb

namespace DerivedCompletion
variable (R) (a : R)

/-- The standard completed augmentation is always invertible on actual H0.
This does not assert invertibility on other cohomology degrees. -/
lemma completedTensorAlgebraAugmentation_h0_isIso
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      (boundedAboveCompletedTensorAlgebraAugmentation R a S T).hom.hom.hom) := by
  apply boundedAboveDerivedCompletion_h0_map_isIso R a
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom
  · change ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R S)).obj
      (ModuleCat.of R T)).IsLE 0
    infer_instance
  · change ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (S ⊗[R] T))).IsLE 0
    infer_instance
  · rw [boundedAboveDerivedTensorAlgebraAugmentation_hom]
    exact derivedTensorAugmentation_h0_isIso (ModuleCat.of R S) (ModuleCat.of R T)

variable (p : ℕ) (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The original completed augmentation gives the F3 comparison without Tor or Koszul hypotheses. -/
def completedTensorH0PDAlgEquiv :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃ₐ[R]
        PDCompletionH0 (S ⊗[R] T) p 0 := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := pdCompletionCommRing (S ⊗[R] T) p 0
  letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  letI := derivedH0CommRing (completedAlgebra R (p : R) (S ⊗[R] T))
  letI := derivedH0Algebra (completedAlgebra R (p : R) (S ⊗[R] T))
  exact (derivedH0AlgEquivOfIsoHomology
    (boundedAboveCompletedTensorAlgebraAugmentation R (p : R) S T)
    (completedTensorAlgebraAugmentation_h0_isIso R (p : R) S T)).trans
      (completedAlgebraH0PDAlgEquiv R (S ⊗[R] T) p)

/-- Its function is the actual completed augmentation followed by the standard F3 comparison. -/
lemma completedTensorH0PDAlgEquiv_apply
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    completedTensorH0PDAlgEquiv R p S T x =
      completedAlgebraH0PDAlgEquiv R (S ⊗[R] T) p
        (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraAugmentation R (p : R) S T) x) := rfl

/-- The comparison preserves the completion unit and the original ordinary tensor H⁰ class. -/
lemma completedTensorH0PDAlgEquiv_unit
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    completedTensorH0PDAlgEquiv R p S T
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
      pdCompletionUnit (S ⊗[R] T) p 0 (derivedTensorH0AlgEquiv S T x) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing (S ⊗[R] T) p 0
  let := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  rw [completedTensorH0PDAlgEquiv_apply, completedTensorH0AlgebraAugmentation_unit]
  have hb : completedAlgebraUnitAlgHom R (p : R) (S ⊗[R] T)
      (derivedTensorH0AlgEquiv S T x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)))
        (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T) x) := by
    rw [completedAlgebraUnitAlgHom_apply]
    have hz : (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R (S ⊗[R] T)) (derivedTensorH0AlgEquiv S T x) =
        derivedH0AlgMap (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T) x := by
      change (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R (S ⊗[R] T))
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
          (ModuleCat.of R (S ⊗[R] T))
          (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T) x)) = _
      exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app
        (ModuleCat.of R (S ⊗[R] T))).toLinearEquiv.symm_apply_apply _
    rw [hz]
  rw [← hb, completedAlgebraH0PDAlgEquiv_unit]

/-- The left factor keeps its original ordinary tensor inclusion in F3. -/
lemma completedTensorH0PDAlgEquiv_left
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    completedTensorH0PDAlgEquiv R p S T
      (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R (p : R) S T) x) =
      pdCompletionUnit (S ⊗[R] T) p 0
        ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
            (ModuleCat.of R S) x)) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing (S ⊗[R] T) p 0
  let := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  rw [boundedAboveCompletedTensorAlgebraLeft, ← derivedH0AlgMap_comp_apply]
  erw [completedTensorH0PDAlgEquiv_unit R p S T]
  rw [derivedTensorH0AlgEquiv_apply, derivedTensorH0AlgHom_left]

/-- The right factor keeps its original ordinary tensor inclusion in F3. -/
lemma completedTensorH0PDAlgEquiv_right
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := pdCompletionCommRing (S ⊗[R] T) p 0
    letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
    completedTensorH0PDAlgEquiv R p S T
      (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraRight R (p : R) S T) x) =
      pdCompletionUnit (S ⊗[R] T) p 0
        ((Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
            (ModuleCat.of R T) x)) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing (S ⊗[R] T) p 0
  let := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  rw [boundedAboveCompletedTensorAlgebraRight, ← derivedH0AlgMap_comp_apply]
  erw [completedTensorH0PDAlgEquiv_unit R p S T]
  rw [derivedTensorH0AlgEquiv_apply, derivedTensorH0AlgHom_right]

end DerivedCompletion
end SerrePositivity

end CompletedTensorH0ComparisonPart

section CompletedTensorClassicalComparisonPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hB : IsSMulRegular (S ⊗[R] T) (p : S ⊗[R] T))
local notation "B" => S ⊗[R] T

/-- Compare the original H0 ring with the classical completion of the ordinary tensor. -/
def completedTensorH0AdicRingEquiv :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃+*
        AdicCompletion (Ideal.span {(p : B)}) B := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := pdCompletionCommRing B p 0
  letI := pdCompletionBaseAlgebra R B p 0
  letI := pairCompletionAlgebra B (p : B) 0
  letI := principalCompletionCommRing B (p : B)
  letI := principalCompletionAlgebra B (p : B)
  exact (completedTensorH0PDAlgEquiv R p S T).toRingEquiv.trans
    ((pairCompletionZeroPrincipalAlgEquiv B (p : B)).toRingEquiv.trans
      (principalCompletionAdicAlgEquiv B (p : B) hB).toRingEquiv)

/-- The ring comparison preserves the original completion unit. -/
lemma completedTensorH0AdicRingEquiv_unit
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    completedTensorH0AdicRingEquiv R p S T hB
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
      algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B) (derivedTensorH0AlgEquiv S T x) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing B p 0
  let := pdCompletionBaseAlgebra R B p 0
  let := pairCompletionAlgebra B (p : B) 0
  let := principalCompletionCommRing B (p : B)
  let := principalCompletionAlgebra B (p : B)
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (completedTensorH0PDAlgEquiv R p S T _)) = _
  rw [completedTensorH0PDAlgEquiv_unit]
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (pairCompletionUnitRingHom B (p : B) 0 _)) = _
  rw [pairCompletionZeroPrincipalAlgEquiv_unit, principalCompletionAdicAlgEquiv_unit]

/-- The original left factor map becomes the standard completed tensor inclusion. -/
lemma completedTensorH0AdicRingEquiv_left
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    completedTensorH0AdicRingEquiv R p S T hB
      (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R (p : R) S T) x) =
      algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)
        ((Algebra.TensorProduct.includeLeft : S →ₐ[R] B)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
            (ModuleCat.of R S) x)) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing B p 0
  let := pdCompletionBaseAlgebra R B p 0
  let := pairCompletionAlgebra B (p : B) 0
  let := principalCompletionCommRing B (p : B)
  let := principalCompletionAlgebra B (p : B)
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (completedTensorH0PDAlgEquiv R p S T _)) = _
  rw [completedTensorH0PDAlgEquiv_left]
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (pairCompletionUnitRingHom B (p : B) 0 _)) = _
  rw [pairCompletionZeroPrincipalAlgEquiv_unit, principalCompletionAdicAlgEquiv_unit]

/-- The original right factor map becomes the standard completed tensor inclusion. -/
lemma completedTensorH0AdicRingEquiv_right
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    completedTensorH0AdicRingEquiv R p S T hB
      (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraRight R (p : R) S T) x) =
      algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)
        ((Algebra.TensorProduct.includeRight : T →ₐ[R] B)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
            (ModuleCat.of R T) x)) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing B p 0
  let := pdCompletionBaseAlgebra R B p 0
  let := pairCompletionAlgebra B (p : B) 0
  let := principalCompletionCommRing B (p : B)
  let := principalCompletionAlgebra B (p : B)
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (completedTensorH0PDAlgEquiv R p S T _)) = _
  rw [completedTensorH0PDAlgEquiv_right]
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (pairCompletionUnitRingHom B (p : B) 0 _)) = _
  rw [pairCompletionZeroPrincipalAlgEquiv_unit, principalCompletionAdicAlgEquiv_unit]

/-- The comparison preserves the original coefficient algebra map. -/
lemma completedTensorH0AdicRingEquiv_algebraMap (r : R) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    completedTensorH0AdicRingEquiv R p S T hB (algebraMap R _ r) =
      algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B) (algebraMap R B r) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := pdCompletionCommRing B p 0
  let := pdCompletionBaseAlgebra R B p 0
  let := pairCompletionAlgebra B (p : B) 0
  let := principalCompletionCommRing B (p : B)
  let := principalCompletionAlgebra B (p : B)
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (completedTensorH0PDAlgEquiv R p S T (algebraMap R _ r))) = _
  rw [(completedTensorH0PDAlgEquiv R p S T).commutes]
  change principalCompletionAdicAlgEquiv B (p : B) hB
    (pairCompletionZeroPrincipalAlgEquiv B (p : B)
      (pairCompletionUnitRingHom B (p : B) 0 (algebraMap R B r))) = _
  rw [pairCompletionZeroPrincipalAlgEquiv_unit, principalCompletionAdicAlgEquiv_unit]
end SerrePositivity.DerivedCompletion

end CompletedTensorClassicalComparisonPart

section CompletedTensorH0RingTransportPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The actual completed tensor H⁰ is the principal completion of the ordinary tensor,
including when the ordinary tensor has unbounded p-power torsion. -/
def completedTensorH0PrincipalRingEquiv :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃+*
        PrincipalCompletionH0 (S ⊗[R] T) (p : S ⊗[R] T) := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := pdCompletionCommRing (S ⊗[R] T) p 0
  letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  letI := pairCompletionAlgebra (S ⊗[R] T) (p : S ⊗[R] T) 0
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  letI := principalCompletionAlgebra (S ⊗[R] T) (p : S ⊗[R] T)
  exact (completedTensorH0PDAlgEquiv R p S T).toRingEquiv.trans
    (pairCompletionZeroPrincipalAlgEquiv (S ⊗[R] T) (p : S ⊗[R] T)).toRingEquiv

/-- The comparison preserves the original algebra completion unit on every H⁰ class. -/
lemma completedTensorH0PrincipalRingEquiv_unit
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
    completedTensorH0PrincipalRingEquiv R p S T
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
      principalCompletionUnitRingHom (S ⊗[R] T) (p : S ⊗[R] T)
        (derivedTensorH0AlgEquiv S T x) := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := pdCompletionCommRing (S ⊗[R] T) p 0
  letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  letI := pairCompletionAlgebra (S ⊗[R] T) (p : S ⊗[R] T) 0
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  letI := principalCompletionAlgebra (S ⊗[R] T) (p : S ⊗[R] T)
  change pairCompletionZeroPrincipalAlgEquiv (S ⊗[R] T) (p : S ⊗[R] T)
    (completedTensorH0PDAlgEquiv R p S T _) = _
  rw [completedTensorH0PDAlgEquiv_unit]
  exact pairCompletionZeroPrincipalAlgEquiv_unit _ _ _

variable (R' : Type u) [CommRing R'] (S' T' : Type u)
    [CommRing S'] [CommRing T'] [Algebra R' S'] [Algebra R' T']

/-- An ordinary tensor ring equivalence induces an equivalence of the original
completed tensor H⁰ rings, even across a change of base ring. -/
def completedTensorH0RingEquivOfTensorRingEquiv
    (e : (S ⊗[R] T) ≃+* (S' ⊗[R'] T')) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R' (p : R') S' T')
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃+*
      (DerivedCategory.homologyFunctor (ModuleCat R') 0).obj
        (boundedAboveCompletedTensorAlgebra R' (p : R') S' T').X.obj := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R' (p : R') S' T')
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  letI := principalCompletionCommRing (S' ⊗[R'] T') (p : S' ⊗[R'] T')
  exact (completedTensorH0PrincipalRingEquiv R p S T).trans
    ((principalCompletionRingEquiv e (p : S ⊗[R] T) (p : S' ⊗[R'] T')
      (map_natCast e p)).trans (completedTensorH0PrincipalRingEquiv R' p S' T').symm)

/-- The transport carries the original completion unit to the original target unit. -/
lemma completedTensorH0RingEquivOfTensorRingEquiv_unit
    (e : (S ⊗[R] T) ≃+* (S' ⊗[R'] T'))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R') S' T')
    letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R') S' T')
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R' (p : R') S' T')
    completedTensorH0RingEquivOfTensorRingEquiv R p S T R' S' T' e
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R' (p : R')
        (boundedAboveDerivedTensorAlgebra (R := R') S' T'))
        ((derivedTensorH0AlgEquiv S' T').symm (e (derivedTensorH0AlgEquiv S T x))) := by
  letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R') S' T')
  letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R') S' T')
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R' (p : R') S' T')
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  letI := principalCompletionCommRing (S' ⊗[R'] T') (p : S' ⊗[R'] T')
  apply (completedTensorH0PrincipalRingEquiv R' p S' T').injective
  change completedTensorH0PrincipalRingEquiv R' p S' T'
      ((completedTensorH0PrincipalRingEquiv R' p S' T').symm
        (principalCompletionRingEquiv e (p : S ⊗[R] T) (p : S' ⊗[R'] T')
          (map_natCast e p) (completedTensorH0PrincipalRingEquiv R p S T _))) = _
  rw [RingEquiv.apply_symm_apply, completedTensorH0PrincipalRingEquiv_unit,
    principalCompletionRingEquiv_unit, completedTensorH0PrincipalRingEquiv_unit,
    AlgEquiv.apply_symm_apply]

/-- Compatible base and factor presentations identify the actual completed H⁰ rings. -/
def completedTensorH0RingEquivOfPresentations
    (e : R ≃+* R') (f : S ≃+* S') (g : T ≃+* T')
    (hf : ∀ r, f (algebraMap R S r) = algebraMap R' S' (e r))
    (hg : ∀ r, g (algebraMap R T r) = algebraMap R' T' (e r)) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R' (p : R') S' T')
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃+*
      (DerivedCategory.homologyFunctor (ModuleCat R') 0).obj
        (boundedAboveCompletedTensorAlgebra R' (p : R') S' T').X.obj :=
  completedTensorH0RingEquivOfTensorRingEquiv R p S T R' S' T'
    (tensorRingEquivOfCompatibleBase e f g hf hg)

end SerrePositivity.DerivedCompletion

end CompletedTensorH0RingTransportPart

section CompletedSurjectiveAlgebraMulPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- The original derived multiplication of a surjective algebra is an H⁰ isomorphism. -/
lemma surjectiveAlgebraMul_h0_isIso
    (A : Type u) [CommRing A] [Algebra R A]
    (hs : Function.Surjective (algebraMap R A)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      (boundedAboveDerivedAlgebraMul (R := R) A).hom) := by
  have hl : IsIso (ModuleCat.ofHom (LinearMap.mul' R A)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (LinearMap.mul'_bijective_of_surjective R A hs)
  have ha := derivedTensorAugmentation_h0_isIso (ModuleCat.of R A) (ModuleCat.of R A)
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app (ModuleCat.of R A) ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R A))))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- Discreteness of the actual completed self-tensor inverts the original completed product.
The coefficient algebra is complete and the original structure map is surjective. -/
lemma completedSurjectiveAlgebraMul_isIso (a : R)
    (A : Type u) [CommRing A] [Algebra R A]
    (hs : Function.Surjective (algebraMap R A))
    (hc : IsModuleComplete R a (ModuleCat.of R A))
    (hpure :
      let X := (boundedAboveDerivedCompletionFunctor R a).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A),
            boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)))
      X.obj.IsGE 0 ∧ X.obj.IsLE 0) :
    IsIso ((derivedComplexCompletionFunctor R a).map
      (boundedAboveDerivedAlgebraMul (R := R) A).hom) := by
  let X := boundedAboveDerivedTensor.obj
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A),
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))
  let Y := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)
  let F := derivedComplexCompletionFunctor R a
  let f : X.obj ⟶ Y.obj := (boundedAboveDerivedAlgebraMul (R := R) A).hom
  letI : Y.obj.IsLE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)).IsLE 0
    infer_instance
  letI : Y.obj.IsGE 0 := by
    change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R A)).IsGE 0
    infer_instance
  have hX : X.obj.IsLE 0 := by
    change (boundedAboveDerivedTensor.obj (Y, Y)).obj.IsLE 0
    infer_instance
  have hY : Y.obj.IsLE 0 := inferInstance
  have h0 := derivedComplexCompletion_h0_map_isIso R a f hX hY
    (surjectiveAlgebraMul_h0_isIso R A hs)
  letI : (F.obj X.obj).IsGE 0 := hpure.1
  letI : (F.obj X.obj).IsLE 0 := hpure.2
  let eY : Y.obj ≅ F.obj Y.obj := derivedComplexCompletionUnitIso R a Y.obj hc
  letI : (F.obj Y.obj).IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso eY 0
  letI : (F.obj Y.obj).IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso eY 0
  apply (DerivedCategory.isIso_iff (ModuleCat R) (F.map f)).mpr
  intro i
  by_cases hi : i = 0
  · subst i
    exact h0
  · have hzX : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj (F.obj X.obj)) := by
      by_cases hpos : 0 < i
      · exact DerivedCategory.isZero_of_isLE _ 0 i hpos
      · exact DerivedCategory.isZero_of_isGE _ 0 i (by omega)
    have hzY : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj (F.obj Y.obj)) := by
      by_cases hpos : 0 < i
      · exact DerivedCategory.isZero_of_isLE _ 0 i hpos
      · exact DerivedCategory.isZero_of_isGE _ 0 i (by omega)
    exact hzX.isIso hzY _

end SerrePositivity.DerivedCompletion

end CompletedSurjectiveAlgebraMulPart
