module

public import SerrePositivity.CommutativeAlgebra.GradedCumulativeGrowth

/-! # Surjective degree-preserving maps and cumulative length bounds

A graded surjection is surjective in each degree. Any submodule killed by the map
can first be factored out; this compares the target growth with that of a relation quotient.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSerre

open DirectSum

set_option backward.isDefEq.respectTransparency false

variable {R M T : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup T] [Module R T]
variable (NS : ℕ → Submodule R M) (NT : ℕ → Submodule R T)
variable [Decomposition NS] [Decomposition NT] (F : M →ₗ[R] T)
variable (hdegree : ∀ n, ∀ x ∈ NS n, F x ∈ NT n)

include hdegree

/-- A degree-preserving linear map commutes with each homogeneous projection. -/
lemma gradeProjection_comp (n : ℕ) :
    (gradeProjection NT n).comp F = F.comp (gradeProjection NS n) := by
  apply DirectSum.decompose_lhom_ext NS
  intro k
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, Submodule.coe_subtype]
  by_cases h : k = n
  · subst k
    rw [gradeProjection_same NT n (hdegree n x x.2), gradeProjection_same NS n x.2]
  · rw [gradeProjection_ne NT n k h (hdegree k x x.2),
      gradeProjection_ne NS n k h x.2, map_zero]

lemma ker_isHomogeneous_of_degree_preserving : F.ker.IsHomogeneous NS := by
  intro n x hx
  change F (gradeProjection NS n x) = 0
  rw [← LinearMap.comp_apply, ← gradeProjection_comp NS NT F hdegree]
  change gradeProjection NT n (F x) = 0
  rw [LinearMap.mem_ker.mp hx, map_zero]

/-- The map on a component, after factoring out a submodule killed by `F`. -/
def quotientGradeMap (S : Submodule R M) (hS : S ≤ F.ker) (n : ℕ) :
    quotientGrade NS S n →ₗ[R] NT n :=
  ((S.liftQ F hS).comp (quotientGrade NS S n).subtype).codRestrict (NT n) (by
    intro x
    obtain ⟨m, hm, heq⟩ := x.2
    change (S.liftQ F hS) (x : M ⧸ S) ∈ NT n
    rw [← heq]
    exact hdegree n m hm)

/-- A global graded surjection remains surjective on each component of a relation quotient. -/
lemma quotientGradeMap_surjective (hf : Function.Surjective F)
    (S : Submodule R M) (hS : S ≤ F.ker) (n : ℕ) :
    Function.Surjective (quotientGradeMap NS NT F hdegree S hS n) := by
  intro y
  obtain ⟨m, hm⟩ := hf (y : T)
  let x : NS n := ⟨gradeProjection NS n m, (DirectSum.decompose NS m n).2⟩
  refine ⟨⟨S.mkQ x, ⟨x, x.2, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change F (gradeProjection NS n m) = (y : T)
  have h := DFunLike.congr_fun (gradeProjection_comp NS NT F hdegree n) m
  simp only [LinearMap.comp_apply] at h
  rw [hm, gradeProjection_same NT n y.2] at h
  exact h.symm

lemma length_le_quotientGrade_of_surjective (hf : Function.Surjective F)
    (S : Submodule R M) (hS : S ≤ F.ker) (n : ℕ) :
    Module.length R (NT n) ≤ Module.length R (quotientGrade NS S n) :=
  Module.length_le_of_surjective (quotientGradeMap NS NT F hdegree S hS n)
    (quotientGradeMap_surjective NS NT F hdegree hf S hS n)

/-- The target cumulative growth is bounded by that of any killed relation quotient. -/
theorem cumulativeLength_le_quotient_of_surjective
    (hfinite : ∀ n, IsFiniteLength R (NS n)) (hf : Function.Surjective F)
    (S : Submodule R M) (hS : S ≤ F.ker) (n : ℕ) :
    cumulativeLength NT n ≤ cumulativeLength (quotientGrade NS S) n := by
  apply Finset.sum_le_sum
  intro i _
  have h := length_le_quotientGrade_of_surjective NS NT F hdegree hf S hS i
  have hq := finiteLength_quotientGrade NS hfinite S i
  exact_mod_cast ENat.toNat_le_toNat h (Module.length_ne_top_iff.mpr hq)

end SerrePositivity.HilbertSerre
