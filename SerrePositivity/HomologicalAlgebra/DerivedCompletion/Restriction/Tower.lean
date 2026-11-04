module

public import SerrePositivity.HomologicalAlgebra.DerivedRestriction
public import SerrePositivity.HomologicalAlgebra.LinearFunctorScalarCone
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # 係数制限と冪 Koszul の塔

## 概要

係数の制限が実際の冪 Koszul の完備化の各段（`restrictionPowerKoszulStageIso`）と、直積と錐による塔の模型（`restrictionTowerHolimIso`・`restrictionComplexCompletionIso`）を保つことを示す。

## 方針

段ごとのスカラーの錐の同型を、塔の直積と差分へ持ち上げる。

## 規約

旧 `RestrictionKoszulStage`・`RestrictionTower`。

## 使われ方

`Restriction/Completion`。
-/

@[expose] public noncomputable section

universe u

section RestrictionKoszulStagePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex
open HomologicalComplex.homotopyCofiber
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Restriction sends the actual scalar endomorphism to its original base-ring scalar. -/
lemma restrictCochain_smulId (a : R) (b : S) (hab : φ a = b)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map (smulId b K) =
      smulId a (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  subst b
  rfl

/-- The canonical additive cone comparison preserves the specified scalar after restriction. -/
def restrictionScalarConeIso (a : R) (b : S) (hab : φ a = b)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mappingCone (smulId b K)) ≅
      CochainComplex.mappingCone (smulId a
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K)) :=
  additiveFunctorCofiberIsoOfEq (ModuleCat.restrictScalars φ) (smulId b K) _
    (restrictCochain_smulId φ a b hab K)

/-- The inverse scalar-cone comparison preserves the original first component inclusion. -/
@[reassoc] lemma restrictionScalarConeIso_inv_inl
    (a : R) (b : S) (hab : φ a = b) (K : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    inlX (smulId a (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K))
        (i + 1) i rfl ≫ (restrictionScalarConeIso φ a b hab K).inv.f i =
      (ModuleCat.restrictScalars φ).map (inlX (smulId b K) (i + 1) i rfl) :=
  additiveFunctorCofiberIsoOfEq_inv_inl _ _ _ _ _

/-- The inverse comparison also preserves the original second component inclusion. -/
@[reassoc] lemma restrictionScalarConeIso_inv_inr
    (a : R) (b : S) (hab : φ a = b) (K : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    inrX (smulId a (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K)) i ≫
        (restrictionScalarConeIso φ a b hab K).inv.f i =
      (ModuleCat.restrictScalars φ).map (inrX (smulId b K) i) :=
  additiveFunctorCofiberIsoOfEq_inv_inr _ _ _ _ _

/-- Restriction compares the actual power-Koszul stages for every natural power. -/
def restrictionPowerKoszulStageIso (a : R)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℕ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
        (complexPowerKoszulStage S (φ a) K n) ≅
      complexPowerKoszulStage R a
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) n :=
  restrictionScalarConeIso φ (a ^ n) ((φ a) ^ n) (map_pow φ a n) K

/-- The inverse comparison is natural in every actual coefficient-complex morphism. -/
@[reassoc] lemma restrictionScalarConeIso_inv_naturality
    (a : R) (b : S) (hab : φ a = b)
    {K L : CochainComplex (ModuleCat.{u} S) ℤ} (f : K ⟶ L) :
    (restrictionScalarConeIso φ a b hab K).inv ≫
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
          ((scalarConeFunctor b).map f) =
      (scalarConeFunctor a).map
          (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map f) ≫
        (restrictionScalarConeIso φ a b hab L).inv := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ext_from_X
    (smulId a (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K))
    (i + 1) i rfl
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      scalarConeFunctor_inl_map_assoc]
    rw [← Category.assoc, restrictionScalarConeIso_inv_inl,
      ← CategoryTheory.Functor.map_comp, scalarConeFunctor_inl_map,
      CategoryTheory.Functor.map_comp, restrictionScalarConeIso_inv_inl]
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      scalarConeFunctor_inr_map_assoc]
    rw [← Category.assoc, restrictionScalarConeIso_inv_inr,
      ← CategoryTheory.Functor.map_comp, scalarConeFunctor_inr_map,
      CategoryTheory.Functor.map_comp, restrictionScalarConeIso_inv_inr]

/-- The standard inclusion into a scalar cone is preserved by coefficient restriction. -/
@[reassoc] lemma restrictionScalarConeIso_inr
    (a : R) (b : S) (hab : φ a = b) (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCone.inr (smulId b K)) ≫
      (restrictionScalarConeIso φ a b hab K).hom =
      CochainComplex.mappingCone.inr (smulId a
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K)) := by
  apply (cancel_mono (restrictionScalarConeIso φ a b hab K).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext i
  exact (restrictionScalarConeIso_inv_inr φ a b hab K i).symm

/-- The actual descending power-Koszul transitions commute with the inverse comparisons. -/
@[reassoc] lemma restrictionPowerKoszulStageIso_inv_transition
    (a : R) (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℕ) :
    (restrictionPowerKoszulStageIso φ a K (n + 1)).inv ≫
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
          (complexPowerKoszulTransition S (φ a) K n) =
      complexPowerKoszulTransition R a
          (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) n ≫
        (restrictionPowerKoszulStageIso φ a K n).inv := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ext_from_X
    (smulId (a ^ (n + 1))
      (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K))
    (i + 1) i rfl
  · simp only [restrictionPowerKoszulStageIso, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, complexPowerKoszulTransition]
    rw [← Category.assoc, restrictionScalarConeIso_inv_inl,
      ← CategoryTheory.Functor.map_comp, moduleConeArrowMap_inl,
      CategoryTheory.Functor.map_comp, moduleConeArrowMap_inl_assoc,
      restrictionScalarConeIso_inv_inl]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · simp only [restrictionPowerKoszulStageIso, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, complexPowerKoszulTransition]
    rw [← Category.assoc, restrictionScalarConeIso_inv_inr,
      ← CategoryTheory.Functor.map_comp, moduleConeArrowMap_inr,
      CategoryTheory.Functor.map_comp, moduleConeArrowMap_inr_assoc,
      restrictionScalarConeIso_inv_inr]
    rfl

/-- The forward comparisons intertwine exactly the original power-Koszul transition maps. -/
@[reassoc] lemma restrictionPowerKoszulStageIso_transition
    (a : R) (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℕ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        (complexPowerKoszulTransition S (φ a) K n) ≫
      (restrictionPowerKoszulStageIso φ a K n).hom =
      (restrictionPowerKoszulStageIso φ a K (n + 1)).hom ≫
        complexPowerKoszulTransition R a
          (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) n := by
  have h := congrArg (fun f ↦ (restrictionPowerKoszulStageIso φ a K (n + 1)).hom ≫ f ≫
    (restrictionPowerKoszulStageIso φ a K n).hom)
    (restrictionPowerKoszulStageIso_inv_transition φ a K n)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

end SerrePositivity.DerivedCompletion

end RestrictionKoszulStagePart

section RestrictionTowerPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
local notation "G" =>
  Functor.mapHomologicalComplex (ModuleCat.restrictScalars φ) (ComplexShape.up ℤ)

/-- Restriction preserves the actual countable product of coefficient complexes. -/
def restrictionTowerProductIso (K : ℕ → CochainComplex (ModuleCat.{u} S) ℤ) :
    (G).obj (piObj K) ≅ piObj (fun n ↦ (G).obj (K n)) :=
  PreservesProduct.iso (G) K

/-- The product comparison preserves each original projection. -/
@[reassoc] lemma restrictionTowerProductIso_hom_projection
    (K : ℕ → CochainComplex (ModuleCat.{u} S) ℤ) (n : ℕ) :
    (restrictionTowerProductIso φ K).hom ≫ Pi.π (fun n ↦ (G).obj (K n)) n =
      (G).map (Pi.π K n) := by
  exact piComparison_comp_π (G) K n

/-- The original difference map is preserved, including the transition term. -/
lemma restrictionTowerDifference
    (K : ℕ → CochainComplex (ModuleCat.{u} S) ℤ) (t : ∀ n, K (n + 1) ⟶ K n) :
    (G).map (complexTowerDifference S K t) ≫ (restrictionTowerProductIso φ K).hom =
      (restrictionTowerProductIso φ K).hom ≫
        complexTowerDifference R (fun n ↦ (G).obj (K n)) (fun n ↦ (G).map (t n)) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, restrictionTowerProductIso_hom_projection,
    ← CategoryTheory.Functor.map_comp, complexTowerDifference_projection]
  rw [Category.assoc, complexTowerDifference_projection, Preadditive.comp_sub]
  rw [← Category.assoc, restrictionTowerProductIso_hom_projection,
    restrictionTowerProductIso_hom_projection]
  simp only [CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_comp]

/-- Restriction preserves the original homotopy-limit complex with its actual cone and shift. -/
def restrictionTowerHolimIso
    (K : ℕ → CochainComplex (ModuleCat.{u} S) ℤ) (t : ∀ n, K (n + 1) ⟶ K n) :
    (G).obj (complexTowerHomotopyLimit S K t) ≅
      complexTowerHomotopyLimit R (fun n ↦ (G).obj (K n)) (fun n ↦ (G).map (t n)) :=
  ((G).commShiftIso (-1 : ℤ)).app (CochainComplex.mappingCone (complexTowerDifference S K t)) ≪≫
    (shiftFunctor (CochainComplex (ModuleCat R) ℤ) (-1 : ℤ)).mapIso
      (homotopyCofiber.mapHomologicalComplexObjIso (complexTowerDifference S K t)
          (ModuleCat.restrictScalars φ) ≪≫
        homotopyCofiber.mapArrowIso _ _ (fun j ↦ ⟨j - 1, by simp⟩)
          (Arrow.isoMk (restrictionTowerProductIso φ K) (restrictionTowerProductIso φ K)
            (restrictionTowerDifference φ K t).symm))

/-- The original completion complexes commute with arbitrary coefficient restriction. -/
def restrictionComplexCompletionIso (a : R)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    (G).obj ((complexCompletionFunctor S (φ a)).obj K) ≅
      (complexCompletionFunctor R a).obj ((G).obj K) :=
  restrictionTowerHolimIso φ (complexPowerKoszulStage S (φ a) K)
      (complexPowerKoszulTransition S (φ a) K) ≪≫
    complexTowerHomotopyLimitIso R
      (K := fun n ↦ (G).obj (complexPowerKoszulStage S (φ a) K n))
      (L := complexPowerKoszulStage R a ((G).obj K))
      (fun n ↦ (G).map (complexPowerKoszulTransition S (φ a) K n))
      (complexPowerKoszulTransition R a ((G).obj K))
      (restrictionPowerKoszulStageIso φ a K)
      (restrictionPowerKoszulStageIso_transition φ a K)

end SerrePositivity.DerivedCompletion

end RestrictionTowerPart
