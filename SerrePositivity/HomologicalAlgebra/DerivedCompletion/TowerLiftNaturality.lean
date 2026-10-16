module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerMap

/-! # Naturality of the original tower lift in its source complex -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)

/-- Precomposing a zero-difference map precomposes its original cone lift. -/
lemma complexTowerHomotopyLimitLift_precomp
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (β : Q ⟶ piObj K) (hβ : β ≫ complexTowerDifference R K t = 0) :
    f ≫ complexTowerHomotopyLimitLift R K t Q β hβ =
      complexTowerHomotopyLimitLift R K t P (f ≫ β)
        (by rw [Category.assoc, hβ, comp_zero]) := by
  apply (Cocycle.equivHomShift (K := P)
    (L := CochainComplex.mappingCone (complexTowerDifference R K t)) (n := (-1 : ℤ))).injective
  rw [Cocycle.equivHomShift_comp (n := (-1 : ℤ))]
  apply Subtype.ext
  simp only [complexTowerHomotopyLimitLift, Cocycle.precomp, Cocycle.mk_coe]
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp only [CochainComplex.mappingCone.liftCocycle_coe, Cocycle.ofHom_coe,
    CochainComplex.mappingCone.liftCochain, Cochain.zero_comp, add_zero]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [← Cochain.ofHom_comp]

/-- The compatible lift keeps the original maps under source precomposition. -/
lemma complexTowerCompatibleLift_precomp
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (β : ∀ n, Q ⟶ K n) (hβ : ∀ n, β (n + 1) ≫ t n = β n) :
    f ≫ complexTowerCompatibleLift R K t Q β hβ =
      complexTowerCompatibleLift R K t P (fun n => f ≫ β n)
        (by intro n; rw [Category.assoc, hβ]) := by
  unfold complexTowerCompatibleLift
  rw [complexTowerHomotopyLimitLift_precomp]
  congr 1
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.lift_comp_π]

/-- Naturality for simultaneous changes of the source and the tower. -/
lemma complexTowerCompatibleLift_naturality
    {L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ} (s : ∀ n, L (n + 1) ⟶ L n)
    (g : ∀ n, K n ⟶ L n) (hg : ∀ n, t n ≫ g n = g (n + 1) ≫ s n)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (α : ∀ n, P ⟶ K n) (hα : ∀ n, α (n + 1) ≫ t n = α n)
    (β : ∀ n, Q ⟶ L n) (hβ : ∀ n, β (n + 1) ≫ s n = β n)
    (h : ∀ n, α n ≫ g n = f ≫ β n) :
    complexTowerCompatibleLift R K t P α hα ≫
      complexTowerHomotopyLimitMap R t s g hg =
        f ≫ complexTowerCompatibleLift R L s Q β hβ := by
  rw [complexTowerCompatibleLift_precomp]
  exact complexTowerCompatibleLift_map R t s g hg P α hα _ _ h

end SerrePositivity.DerivedCompletion
