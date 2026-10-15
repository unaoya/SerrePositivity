module

public import SerrePositivity.HomologicalAlgebra.CochainIdempotent
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Degreewise properties and homology of idempotent images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

namespace CochainIdempotent
variable {K : CochainComplex (ModuleCat.{u} R) ℤ}

@[simp, reassoc]
lemma inclusion_projection_f (e : CochainIdempotent K) (n : ℤ) :
    e.inclusion.f n ≫ e.projection.f n = 𝟙 (e.image.X n) := by
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
    congrArg (fun f => f.f n) e.inclusion_projection

lemma projection_f_surjective (e : CochainIdempotent K) (n : ℤ) :
    Function.Surjective (e.projection.f n).hom := by
  intro x
  refine ⟨(e.inclusion.f n).hom x, ?_⟩
  have h := congrArg (fun f => f.hom x) (e.inclusion_projection_f n)
  exact h

lemma image_finite_X (e : CochainIdempotent K) (n : ℤ) [Module.Finite R (K.X n)] :
    Module.Finite R (e.image.X n) :=
  Module.Finite.of_surjective (e.projection.f n).hom (e.projection_f_surjective n)

lemma image_projective_X (e : CochainIdempotent K) (n : ℤ) [Module.Projective R (K.X n)] :
    Module.Projective R (e.image.X n) := by
  apply Module.Projective.of_split (e.inclusion.f n).hom (e.projection.f n).hom
  exact congrArg (fun f => f.hom) (e.inclusion_projection_f n)

lemma image_isZero_X (e : CochainIdempotent K) (n : ℤ) (h : IsZero (K.X n)) :
    IsZero (e.image.X n) := by
  rw [IsZero.iff_id_eq_zero, ← e.inclusion_projection_f n]
  rw [h.eq_of_tgt (e.inclusion.f n) 0, zero_comp]

@[simp, reassoc]
lemma homology_inclusion_projection (e : CochainIdempotent K) (n : ℤ) :
    HomologicalComplex.homologyMap e.inclusion n ≫
      HomologicalComplex.homologyMap e.projection n = 𝟙 (e.image.homology n) := by
  rw [← HomologicalComplex.homologyMap_comp, e.inclusion_projection,
    HomologicalComplex.homologyMap_id]

lemma homology_inclusion_injective (e : CochainIdempotent K) (n : ℤ) :
    Function.Injective (HomologicalComplex.homologyMap e.inclusion n).hom := by
  intro x y h
  have hx := congrArg (fun f => f.hom x) (e.homology_inclusion_projection n)
  have hy := congrArg (fun f => f.hom y) (e.homology_inclusion_projection n)
  exact hx.symm.trans ((congrArg (HomologicalComplex.homologyMap e.projection n).hom h).trans hy)

end CochainIdempotent
end SerrePositivity
