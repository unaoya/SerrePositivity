module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.UniformZeroTower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorSequence

/-! # Holim homology vanishes for uniformly zero homology towers -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)

/-- The actual composite in the category of complexes. -/
def complexTowerComposite (n : ℕ) : ∀ k : ℕ, K (n + k) ⟶ K n
  | 0 => 𝟙 _
  | k + 1 => t (n + k) ≫ complexTowerComposite n k

/-- Taking homology preserves the full transition composite. -/
theorem complexTowerComposite_homology (n k : ℕ) (i : ℤ) :
    moduleTowerComposite R (fun n ↦ (K n).homology i)
      (fun n ↦ (HomologicalComplex.homologyMap (t n) i).hom) n k =
        (HomologicalComplex.homologyMap (complexTowerComposite R K t n k) i).hom := by
  induction k with
  | zero => simp [moduleTowerComposite, complexTowerComposite]
  | succ k ih =>
    simp only [moduleTowerComposite, complexTowerComposite,
      HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, ih]

/-- A uniform zero composite in two adjacent homology towers kills holim homology.
The two lengths can differ, and no stage is assumed acyclic. -/
theorem complexTowerHolim_homology_isZero_of_uniform_zero (i : ℤ)
    (N₀ N₁ : ℕ)
    (h₀ : ∀ n, moduleTowerComposite R (fun n ↦ (K n).homology (i - 1))
      (fun n ↦ (HomologicalComplex.homologyMap (t n) (i - 1)).hom) n N₀ = 0)
    (h₁ : ∀ n, moduleTowerComposite R (fun n ↦ (K n).homology i)
      (fun n ↦ (HomologicalComplex.homologyMap (t n) i).hom) n N₁ = 0) :
    IsZero ((complexTowerHomotopyLimit R K t).homology i) := by
  have hs := (moduleTowerDifference_bijective_of_uniform_zero R
    (fun n ↦ (K n).homology (i - 1))
    (fun n ↦ (HomologicalComplex.homologyMap (t n) (i - 1)).hom) N₀ h₀).2
  have hi := complexTowerMilnorProjection_injective_of_surjective R K t i hs
  have := moduleTowerLimit_subsingleton_of_uniform_zero R
    (fun n ↦ (K n).homology i)
    (fun n ↦ (HomologicalComplex.homologyMap (t n) i).hom) N₁ h₁
  exact ModuleCat.isZero_iff_subsingleton.mpr hi.subsingleton

/-- A uniform zero composite of chain maps makes the actual holim acyclic. -/
theorem complexTowerHolim_acyclic_of_uniform_zero (N : ℕ)
    (h : ∀ n, complexTowerComposite R K t n N = 0) :
    (complexTowerHomotopyLimit R K t).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply complexTowerHolim_homology_isZero_of_uniform_zero R K t i N N
  all_goals
    intro n
    rw [complexTowerComposite_homology, h]
    simp

end SerrePositivity.DerivedCompletion
