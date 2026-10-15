module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionKoszulStage
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerIso
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Coefficient restriction preserves the original product-and-cone tower model -/
@[expose] public noncomputable section
universe u
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
