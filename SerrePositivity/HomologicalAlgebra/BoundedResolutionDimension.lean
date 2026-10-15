module
public import SerrePositivity.HomologicalAlgebra.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-! # A bounded projective resolution bounds projective dimension -/
@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory Limits Abelian
variable {R : Type u} [CommRing R]

/-- A bounded projective resolution supplies the categorical finite-projective-dimension bound. -/
lemma exists_projectiveDimensionLE_of_boundedResolution {M : ModuleCat.{u} R}
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F M)
    (hb : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (F.X i)) :
    ∃ n, HasProjectiveDimensionLE M n := by
  obtain ⟨a, b, hb⟩ := hb
  let n := (-a).toNat
  let P := hF.toProjectiveResolution
  refine ⟨n, HasProjectiveDimensionLT.mk ?_⟩
  intro i hi Y e
  have hz : IsZero (P.complex.X i) := by
    have ht : IsZero (F.X (embUp.f i)) := hb _ (Or.inl (by
      simp only [embUp, ComplexShape.embeddingUpIntLE_f]
      dsimp [n] at hi
      omega))
    exact ht.of_iso (F.restrictionXIso embUp rfl).symm
  obtain ⟨f, hf, he⟩ := P.extMk_surjective e (i + 1) rfl
  have hf0 : f = 0 := hz.eq_zero_of_src f
  rw [← he]
  simp only [hf0, ProjectiveResolution.extMk_zero]

end SerrePositivity
