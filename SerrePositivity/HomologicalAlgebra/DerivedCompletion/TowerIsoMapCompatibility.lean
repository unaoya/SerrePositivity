module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerIso
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerMap

/-! # Standard tower maps agree with the existing tower isomorphisms -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (e : ∀ n, K n ≅ L n)
    (he : ∀ n, t n ≫ (e n).hom = (e (n + 1)).hom ≫ s n)

/-- The original map on holims is exactly the hom of the existing comparison iso. -/
lemma complexTowerHomotopyLimitMap_eq_iso_hom :
    complexTowerHomotopyLimitMap R t s (fun n => (e n).hom) he =
      (complexTowerHomotopyLimitIso R t s e he).hom := rfl

/-- Transporting a compatible lift through a tower iso keeps all original maps. -/
lemma complexTowerCompatibleLift_iso
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (α : ∀ n, P ⟶ K n) (hα : ∀ n, α (n + 1) ≫ t n = α n)
    (β : ∀ n, P ⟶ L n) (hβ : ∀ n, β (n + 1) ≫ s n = β n)
    (hαβ : ∀ n, α n ≫ (e n).hom = β n) :
    complexTowerCompatibleLift R K t P α hα ≫
      (complexTowerHomotopyLimitIso R t s e he).hom =
        complexTowerCompatibleLift R L s P β hβ := by
  rw [← complexTowerHomotopyLimitMap_eq_iso_hom]
  exact complexTowerCompatibleLift_map R t s (fun n => (e n).hom) he P α hα β hβ hαβ

end SerrePositivity.DerivedCompletion
