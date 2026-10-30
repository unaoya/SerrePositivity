module

public import SerrePositivity.HomologicalAlgebra.Complex.Basic

/-! # Cubic chain actions and their scalar and binary-sum constructions

These constructions require neither an inverse for 3 nor perfectness or support hypotheses.
Fourier projectors and character classes are defined in subsequent files.
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

structure CochainCubicAction (K : CochainComplex (ModuleCat.{u} R) ℤ) where
  map : K ⟶ K
  cube : map ≫ map ≫ map = 𝟙 K

namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

@[ext]
lemma ext {τ σ : CochainCubicAction K} (h : τ.map = σ.map) : τ = σ := by
  cases τ
  cases σ
  cases h
  rfl

/-- A scalar cube root of unity acts on any cochain complex. -/
def scalar (K : CochainComplex (ModuleCat.{u} R) ℤ) (c : R) (hc : c ^ 3 = 1) :
    CochainCubicAction K where
  map := c • 𝟙 K
  cube := by
    simp only [Linear.smul_comp, Linear.comp_smul, id_comp, smul_smul]
    rw [← pow_two, ← pow_succ, hc, one_smul]

@[simp]
lemma scalar_map (K : CochainComplex (ModuleCat.{u} R) ℤ) (c : R) (hc : c ^ 3 = 1) :
    (scalar K c hc).map = c • 𝟙 K := rfl

/-- The diagonal cubic action on a binary sum. -/
def biprod (τ : CochainCubicAction K) (σ : CochainCubicAction L) :
    CochainCubicAction (K ⊞ L) where
  map := Limits.biprod.map τ.map σ.map
  cube := by
    apply Limits.biprod.hom_ext'
    · simp only [Limits.biprod.inl_map_assoc, Limits.biprod.inl_map, comp_id]
      simpa only [Category.assoc, id_comp] using
        congrArg (fun f => f ≫ (Limits.biprod.inl : K ⟶ K ⊞ L)) τ.cube
    · simp only [Limits.biprod.inr_map_assoc, Limits.biprod.inr_map, comp_id]
      simpa only [Category.assoc, id_comp] using
        congrArg (fun f => f ≫ (Limits.biprod.inr : L ⟶ K ⊞ L)) σ.cube

@[simp]
lemma biprod_map (τ : CochainCubicAction K) (σ : CochainCubicAction L) :
    (τ.biprod σ).map = Limits.biprod.map τ.map σ.map := rfl

end CochainCubicAction
end SerrePositivity
