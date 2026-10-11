module

public import SerrePositivity.CommutativeAlgebra.GradedHilbertSeries

/-! # Homogeneous maps with an arbitrary nonnegative degree shift

Multiplication by a homogeneous relation need not have degree one. These maps
give exact sequences in each degree and the corresponding Hilbert-series identity.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSerre.ShiftMap

open DirectSum

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
variable (N : ℕ → Submodule R M) [Decomposition N] (f : M →ₗ[R] M) (d : ℕ)
variable (hdegree : ∀ n, ∀ x ∈ N n, f x ∈ N (n + d))

include hdegree

lemma gradeProjection_add_comp (n : ℕ) :
    (gradeProjection N (n + d)).comp f = f.comp (gradeProjection N n) := by
  apply DirectSum.decompose_lhom_ext N
  intro k
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, Submodule.coe_subtype]
  by_cases h : k = n
  · subst k
    rw [gradeProjection_same N (n + d) (hdegree n x x.2), gradeProjection_same N n x.2]
  · rw [gradeProjection_ne N (n + d) (k + d) (by omega) (hdegree k x x.2),
      gradeProjection_ne N n k h x.2, map_zero]

lemma gradeProjection_below_comp (n : ℕ) (hn : n < d) :
    (gradeProjection N n).comp f = 0 := by
  apply DirectSum.decompose_lhom_ext N
  intro k
  apply LinearMap.ext
  intro x
  change gradeProjection N n (f x) = 0
  exact gradeProjection_ne N n (k + d) (by omega) (hdegree k x x.2)

lemma kernel_isHomogeneous : f.ker.IsHomogeneous N := by
  intro n x hx
  change f (gradeProjection N n x) = 0
  rw [← LinearMap.comp_apply, ← gradeProjection_add_comp N f d hdegree]
  change gradeProjection N (n + d) (f x) = 0
  rw [LinearMap.mem_ker.mp hx, map_zero]

lemma range_isHomogeneous : f.range.IsHomogeneous N := by
  intro n x hx
  obtain ⟨y, rfl⟩ := hx
  by_cases hn : d ≤ n
  · have h := DFunLike.congr_fun (gradeProjection_add_comp N f d hdegree (n - d)) y
    rw [Nat.sub_add_cancel hn] at h
    exact ⟨gradeProjection N (n - d) y, h.symm⟩
  · have h := DFunLike.congr_fun (gradeProjection_below_comp N f d hdegree n (by omega)) y
    change gradeProjection N n (f y) ∈ f.range
    rw [show gradeProjection N n (f y) = 0 from h]
    exact Submodule.zero_mem _

def componentMap (n : ℕ) : N n →ₗ[R] N (n + d) :=
  (f.comp (N n).subtype).codRestrict (N (n + d)) (fun x => hdegree n x x.2)

omit [Decomposition N] in
lemma componentMap_injective (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (componentMap N f d hdegree n) := by
  intro x y h
  apply Subtype.ext
  exact hf (congrArg Subtype.val h)

lemma componentMap_quotientComponent_exact (n : ℕ) :
    Function.Exact (componentMap N f d hdegree n) (quotientComponent N f (n + d)) := by
  intro x
  constructor
  · intro hx
    have hx0 : f.range.mkQ (x : M) = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx0
    refine ⟨⟨gradeProjection N n y, (DirectSum.decompose N y n).2⟩, ?_⟩
    apply Subtype.ext
    have h := DFunLike.congr_fun (gradeProjection_add_comp N f d hdegree n) y
    exact h.symm.trans (by
      change gradeProjection N (n + d) (f y) = (x : M)
      rw [hy, gradeProjection_same N (n + d) x.2])
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change f.range.mkQ (f y) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩

lemma quotientComponent_below_injective (n : ℕ) (hn : n < d) :
    Function.Injective (quotientComponent N f n) := by
  rw [← LinearMap.ker_eq_bot]
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hx0 : f.range.mkQ (x : M) = 0 := congrArg Subtype.val hx
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx0
  apply Subtype.ext
  have h := DFunLike.congr_fun (gradeProjection_below_comp N f d hdegree n hn) y
  change gradeProjection N n (f y) = 0 at h
  rw [hy, gradeProjection_same N n x.2] at h
  exact h

/-- Below the degree of the relation the quotient has the original components. -/
lemma length_quotientGrade_below (n : ℕ) (hn : n < d) :
    Module.length R (quotientGrade N f.range n) = Module.length R (N n) :=
  (LinearEquiv.ofBijective (quotientComponent N f n)
    ⟨quotientComponent_below_injective N f d hdegree n hn,
      quotientComponent_surjective N f n⟩).length_eq.symm

/-- Multiplication by a nonzero homogeneous relation in a domain gives this exact sequence. -/
lemma length_component_eq_add (hf : Function.Injective f) (n : ℕ) :
    Module.length R (N (n + d)) =
      Module.length R (N n) + Module.length R (quotientGrade N f.range (n + d)) :=
  Module.length_eq_add_of_exact (componentMap N f d hdegree n)
    (quotientComponent N f (n + d)) (componentMap_injective N f d hdegree hf n)
    (quotientComponent_surjective N f (n + d))
    (componentMap_quotientComponent_exact N f d hdegree n)

/-- The Hilbert series of the quotient by an injective degree-`d` map is `(1-X^d)H`. -/
theorem lengthSeries_quotient_eq (hfinite : ∀ n, IsFiniteLength R (N n))
    (hf : Function.Injective f) :
    lengthSeries (quotientGrade N f.range) =
      (1 - PowerSeries.X ^ d) * lengthSeries N := by
  ext n
  simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul',
    lengthSeries, PowerSeries.coeff_mk]
  by_cases hn : d ≤ n
  · rw [ite_eq_left hn]
    have h := length_component_eq_add N f d hdegree hf (n - d)
    rw [Nat.sub_add_cancel hn] at h
    have hq := finiteLength_quotientGrade N hfinite f.range n
    have hc := congrArg (fun a : ℕ∞ => (a.toNat : ℚ)) h
    rw [ENat.toNat_add (Module.length_ne_top_iff.mpr (hfinite (n - d)))
      (Module.length_ne_top_iff.mpr hq), Nat.cast_add] at hc
    linarith
  · rw [ite_eq_right hn, sub_zero, length_quotientGrade_below N f d hdegree n (by omega)]

end SerrePositivity.HilbertSerre.ShiftMap
