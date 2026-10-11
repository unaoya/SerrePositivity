module

public import SerrePositivity.CommutativeAlgebra.GradedSubquotient
public import Mathlib.RingTheory.Length

/-! # 次数一の線形写像の核・余核

次数を一つ上げる写像は成分射影と両立し、その核と像は同次である。
各次数の核・余核を実際の部分加群と商加群として扱う。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSerre

open DirectSum
open scoped DirectSum

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
variable (N : ℕ → Submodule R M) [Decomposition N] (f : M →ₗ[R] M)
variable (hdegree : ∀ n, ∀ x ∈ N n, f x ∈ N (n + 1))

include hdegree

lemma gradeProjection_succ_comp (n : ℕ) :
    (gradeProjection N (n + 1)).comp f = f.comp (gradeProjection N n) := by
  apply DirectSum.decompose_lhom_ext N
  intro k
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, Submodule.coe_subtype]
  by_cases h : k = n
  · subst k
    rw [gradeProjection_same N (n + 1) (hdegree n x x.2), gradeProjection_same N n x.2]
  · rw [gradeProjection_ne N (n + 1) (k + 1) (by omega) (hdegree k x x.2),
      gradeProjection_ne N n k h x.2, map_zero]

lemma gradeProjection_zero_comp : (gradeProjection N 0).comp f = 0 := by
  apply DirectSum.decompose_lhom_ext N
  intro k
  apply LinearMap.ext
  intro x
  change gradeProjection N 0 (f x) = 0
  exact gradeProjection_ne N 0 (k + 1) (by omega) (hdegree k x x.2)

lemma kernel_isHomogeneous : f.ker.IsHomogeneous N := by
  intro n x hx
  change f (gradeProjection N n x) = 0
  rw [← LinearMap.comp_apply, ← gradeProjection_succ_comp N f hdegree]
  change gradeProjection N (n + 1) (f x) = 0
  rw [LinearMap.mem_ker.mp hx, map_zero]

lemma range_isHomogeneous : f.range.IsHomogeneous N := by
  intro n x hx
  obtain ⟨y, rfl⟩ := hx
  cases n with
  | zero =>
    have h := DFunLike.congr_fun (gradeProjection_zero_comp N f hdegree) y
    change gradeProjection N 0 (f y) ∈ f.range
    rw [show gradeProjection N 0 (f y) = 0 from h]
    exact Submodule.zero_mem _
  | succ n =>
    have h := DFunLike.congr_fun (gradeProjection_succ_comp N f hdegree (n := n)) y
    exact ⟨gradeProjection N n y, h.symm⟩

/-- 第 n 次成分から第 n+1 次成分への写像。 -/
def componentMap (n : ℕ) : N n →ₗ[R] N (n + 1) :=
  (f.comp (N n).subtype).codRestrict (N (n + 1)) (fun x => hdegree n x x.2)

/-- 第 n 次の核と、全体の核の第 n 次成分の一致。 -/
def kernelGradeEquiv (n : ℕ) : submoduleGrade N f.ker n ≃ₗ[R] (componentMap N f hdegree n).ker where
  toFun x := ⟨⟨x.1.1, x.2⟩, Subtype.ext x.1.2⟩
  invFun x := ⟨⟨x.1.1, congrArg Subtype.val x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 全体の余核へ写すと、第 n 次成分の像が余核の第 n 次成分となる。 -/
def quotientComponent (n : ℕ) : N n →ₗ[R] quotientGrade N f.range n :=
  (f.range.mkQ.comp (N n).subtype).codRestrict _ (fun x => ⟨x, x.2, rfl⟩)

omit [Decomposition N] hdegree in
lemma quotientComponent_surjective (n : ℕ) : Function.Surjective (quotientComponent N f n) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := y.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

lemma componentMap_quotientComponent_exact (n : ℕ) :
    Function.Exact (componentMap N f hdegree n) (quotientComponent N f (n + 1)) := by
  intro x
  constructor
  · intro hx
    have hx0 : f.range.mkQ (x : M) = 0 := congrArg Subtype.val hx
    have hxmem : (x : M) ∈ f.range := (Submodule.Quotient.mk_eq_zero _).mp hx0
    obtain ⟨y, hy⟩ := hxmem
    refine ⟨⟨gradeProjection N n y, (DirectSum.decompose N y n).2⟩, ?_⟩
    apply Subtype.ext
    have h := DFunLike.congr_fun (gradeProjection_succ_comp N f hdegree (n := n)) y
    exact h.symm.trans (by
      change gradeProjection N (n + 1) (f y) = (x : M)
      rw [hy, gradeProjection_same N (n + 1) x.2])
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change f.range.mkQ (f y) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩

lemma quotientComponent_zero_injective : Function.Injective (quotientComponent N f 0) := by
  rw [← LinearMap.ker_eq_bot]
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hx0 : f.range.mkQ (x : M) = 0 := congrArg Subtype.val hx
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx0
  apply Subtype.ext
  have h := DFunLike.congr_fun (gradeProjection_zero_comp N f hdegree) y
  change gradeProjection N 0 (f y) = 0 at h
  rw [hy, gradeProjection_same N 0 x.2] at h
  exact h

end SerrePositivity.HilbertSerre
