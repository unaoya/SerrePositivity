module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorNaturality

/-! # Zero stage actions and composites on the actual holim homology

One tower map vanishing on Hⁱ and a second vanishing on Hⁱ⁻¹ have zero
composite on Hⁱ(holim). No disappearance of the lim¹ term is assumed.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (g : ∀ n, K n ⟶ L n) (hg : ∀ n, t n ≫ g n = g (n + 1) ≫ s n)

lemma complexTowerHomologyLimitMap_eq_zero (i : ℤ)
    (h : ∀ n, HomologicalComplex.homologyMap (g n) i = 0) :
    complexTowerHomologyLimitMap R t s g hg i = 0 := by
  ext x n
  change HomologicalComplex.homologyMap (g n) i (x.val n) = 0
  rw [h n]
  rfl

lemma complexTowerHomologyLimOneMap_eq_zero (i : ℤ)
    (h : ∀ n, HomologicalComplex.homologyMap (g n) i = 0) :
    complexTowerHomologyLimOneMap R t s g hg i = 0 := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    change Submodule.Quotient.mk (complexTowerHomologyProductMap R g i y) = 0
    have hy : complexTowerHomologyProductMap R g i y = 0 := by
      ext n
      change HomologicalComplex.homologyMap (g n) i (y n) = 0
      rw [h n]
      rfl
    rw [hy]
    rfl

/-- Two maps killing the adjacent stage degrees have zero composite on holim Hⁱ. -/
lemma complexTowerHomotopyLimitMap_homology_comp_eq_zero
    {V : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (v : ∀ n, V (n + 1) ⟶ V n) (h : ∀ n, L n ⟶ V n)
    (hh : ∀ n, s n ≫ h n = h (n + 1) ≫ v n) (i : ℤ)
    (hg₀ : ∀ n, HomologicalComplex.homologyMap (g n) i = 0)
    (hh₀ : ∀ n, HomologicalComplex.homologyMap (h n) (i - 1) = 0) :
    HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i ≫
      HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R s v h hh) i = 0 := by
  ext x
  have hx : complexTowerMilnorProjection R L s i
      (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x) = 0 := by
    rw [complexTowerMilnorProjection_naturality,
      complexTowerHomologyLimitMap_eq_zero R t s g hg i hg₀]
    rfl
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (complexTowerMilnorSequence_shortExact R L s i).exact _ hx
  change HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R s v h hh) i
    (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x) = 0
  change complexTowerMilnorInclusion R L s i y = _ at hy
  rw [← hy, complexTowerMilnorInclusion_naturality,
    complexTowerHomologyLimOneMap_eq_zero R s v h hh (i - 1) hh₀]
  exact map_zero _

end SerrePositivity.DerivedCompletion
