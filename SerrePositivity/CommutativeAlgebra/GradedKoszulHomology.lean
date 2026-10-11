module

public import SerrePositivity.CommutativeAlgebra.GradedSubquotient
public import SerrePositivity.CommutativeAlgebra.HilbertSerreFinite
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Homology gradings for differentials of degree one

Kernels and images of degree-one maps between different graded modules are
homogeneous. Their cycle/image quotient inherits a decomposition, which can be
transported to the categorical homology object.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.GradedKoszul

open DirectSum
open SerrePositivity.HilbertSerre
open CategoryTheory

set_option backward.isDefEq.respectTransparency false

variable {R M N L : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup L] [Module R L]

section degreeOne

variable (NS : ℕ → Submodule R M) (NT : ℕ → Submodule R N)
variable [Decomposition NS] [Decomposition NT] (f : M →ₗ[R] N)
variable (hdegree : ∀ n, ∀ x ∈ NS n, f x ∈ NT (n + 1))

include hdegree

lemma gradeProjection_succ_comp (n : ℕ) :
    (gradeProjection NT (n + 1)).comp f = f.comp (gradeProjection NS n) := by
  apply DirectSum.decompose_lhom_ext NS
  intro k
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, Submodule.coe_subtype]
  by_cases h : k = n
  · subst k
    rw [gradeProjection_same NT (n + 1) (hdegree n x x.2), gradeProjection_same NS n x.2]
  · rw [gradeProjection_ne NT (n + 1) (k + 1) (by omega) (hdegree k x x.2),
      gradeProjection_ne NS n k h x.2, map_zero]

lemma gradeProjection_zero_comp : (gradeProjection NT 0).comp f = 0 := by
  apply DirectSum.decompose_lhom_ext NS
  intro k
  apply LinearMap.ext
  intro x
  exact gradeProjection_ne NT 0 (k + 1) (by omega) (hdegree k x x.2)

lemma kernel_isHomogeneous_of_degree_one : f.ker.IsHomogeneous NS := by
  intro n x hx
  change f (gradeProjection NS n x) = 0
  rw [← LinearMap.comp_apply, ← gradeProjection_succ_comp NS NT f hdegree]
  change gradeProjection NT (n + 1) (f x) = 0
  rw [LinearMap.mem_ker.mp hx, map_zero]

lemma range_isHomogeneous_of_degree_one : f.range.IsHomogeneous NT := by
  intro n x hx
  obtain ⟨y, rfl⟩ := hx
  cases n with
  | zero =>
    have h := DFunLike.congr_fun (gradeProjection_zero_comp NS NT f hdegree) y
    change gradeProjection NT 0 (f y) ∈ f.range
    rw [show gradeProjection NT 0 (f y) = 0 from h]
    exact Submodule.zero_mem _
  | succ n =>
    have h := DFunLike.congr_fun (gradeProjection_succ_comp NS NT f hdegree n) y
    exact ⟨gradeProjection NS n y, h.symm⟩

end degreeOne

/-- Transport an internal homogeneous decomposition along a linear equivalence. -/
theorem isInternal_map_equiv (NS : ℕ → Submodule R M) [Decomposition NS]
    (e : M ≃ₗ[R] N) : DirectSum.IsInternal (fun n => (NS n).map e.toLinearMap) := by
  let p (n : ℕ) : N →ₗ[R] N :=
    e.toLinearMap.comp ((gradeProjection NS n).comp e.symm.toLinearMap)
  apply isInternal_of_projections (fun n => (NS n).map e.toLinearMap) p
  · intro n x
    obtain ⟨m, hm, heq⟩ := x.2
    change e (gradeProjection NS n (e.symm (x : N))) = x
    rw [← heq]
    change e (gradeProjection NS n (e.symm (e m))) = e m
    rw [e.symm_apply_apply, gradeProjection_same NS n hm]
  · intro n k hkn x
    obtain ⟨m, hm, heq⟩ := x.2
    change e (gradeProjection NS n (e.symm (x : N))) = 0
    rw [← heq]
    change e (gradeProjection NS n (e.symm (e m))) = 0
    rw [e.symm_apply_apply, gradeProjection_ne NS n k hkn hm, map_zero]
  · rw [← Submodule.map_iSup, (Decomposition.isInternal NS).submodule_iSup_eq_top,
      Submodule.map_top, LinearEquiv.range]

/-- The product grading on a product of graded modules is an internal direct sum. -/
theorem isInternal_prod (NS : ℕ → Submodule R M) (NT : ℕ → Submodule R N)
    [Decomposition NS] [Decomposition NT] :
    DirectSum.IsInternal (fun n => (NS n).prod (NT n)) := by
  let p (n : ℕ) : M × N →ₗ[R] M × N :=
    (gradeProjection NS n).prodMap (gradeProjection NT n)
  apply isInternal_of_projections (fun n => (NS n).prod (NT n)) p
  · intro n x
    exact Prod.ext (gradeProjection_same NS n x.2.1) (gradeProjection_same NT n x.2.2)
  · intro n k hkn x
    exact Prod.ext (gradeProjection_ne NS n k hkn x.2.1)
      (gradeProjection_ne NT n k hkn x.2.2)
  · apply top_unique
    intro x _
    have hleft : ∀ m : M, (m, (0 : N)) ∈ ⨆ n, (NS n).prod (NT n) := by
      intro m
      induction m using DirectSum.Decomposition.inductionOn NS with
      | zero => exact Submodule.zero_mem _
      | @homogeneous n m =>
        exact (le_iSup (fun n => (NS n).prod (NT n)) n)
          ⟨m.2, Submodule.zero_mem _⟩
      | add a b ha hb =>
        simpa using Submodule.add_mem (⨆ n, (NS n).prod (NT n)) ha hb
    have hright : ∀ n : N, ((0 : M), n) ∈ ⨆ n, (NS n).prod (NT n) := by
      intro m
      induction m using DirectSum.Decomposition.inductionOn NT with
      | zero => exact Submodule.zero_mem _
      | @homogeneous n m =>
        exact (le_iSup (fun n => (NS n).prod (NT n)) n)
          ⟨Submodule.zero_mem _, m.2⟩
      | add a b ha hb =>
        simpa using Submodule.add_mem (⨆ n, (NS n).prod (NT n)) ha hb
    have hx := Submodule.add_mem (⨆ n, (NS n).prod (NT n)) (hleft x.1) (hright x.2)
    simpa using hx

section homology

variable (NS : ℕ → Submodule R M) (NT : ℕ → Submodule R N) (NU : ℕ → Submodule R L)
variable [Decomposition NS] [Decomposition NT] [Decomposition NU]
variable (f : M →ₗ[R] N) (g : N →ₗ[R] L) (hfg : g.comp f = 0)
variable (hf : ∀ n, ∀ x ∈ NS n, f x ∈ NT (n + 1))
variable (hg : ∀ n, ∀ x ∈ NT n, g x ∈ NU (n + 1))

/-- The boundary map with its codomain restricted to the cycles. -/
def toCycles : M →ₗ[R] g.ker :=
  f.codRestrict g.ker (fun x => by
    change g (f x) = 0
    exact DFunLike.congr_fun hfg x)

/-- The explicit module of homology classes. -/
abbrev LinearHomology := g.ker ⧸ (toCycles f g hfg).range

/-- The homogeneous grading of explicit homology classes. -/
def linearHomologyGrade (n : ℕ) : Submodule R (LinearHomology f g hfg) :=
  quotientGrade (submoduleGrade NT g.ker) (toCycles f g hfg).range n

include hf hg in
theorem isInternal_linearHomologyGrade :
    DirectSum.IsInternal (linearHomologyGrade NT f g hfg) := by
  let : Decomposition (submoduleGrade NT g.ker) :=
    (isInternal_submoduleGrade NT g.ker
      (kernel_isHomogeneous_of_degree_one NT NU g hg)).chooseDecomposition
  apply isInternal_quotientGrade
  apply range_isHomogeneous_of_degree_one NS (submoduleGrade NT g.ker) (toCycles f g hfg)
  intro n x hx
  exact hf n x hx

/-- The explicit quotient identifies with the categorical homology. -/
def linearHomologyEquiv :
    LinearHomology f g hfg ≃ₗ[R] (CategoryTheory.ShortComplex.moduleCatMk f g hfg).homology :=
  (CategoryTheory.ShortComplex.moduleCatMk f g hfg).moduleCatHomologyIso.toLinearEquiv.symm

/-- The grading of the categorical homology object. -/
def homologyGrade (n : ℕ) :
    Submodule R (CategoryTheory.ShortComplex.moduleCatMk f g hfg).homology :=
  (linearHomologyGrade NT f g hfg n).map (linearHomologyEquiv f g hfg).toLinearMap

include hf hg in
theorem isInternal_homologyGrade : DirectSum.IsInternal (homologyGrade NT f g hfg) := by
  let : Decomposition (linearHomologyGrade NT f g hfg) :=
    (isInternal_linearHomologyGrade NS NT NU f g hfg hf hg).chooseDecomposition
  exact isInternal_map_equiv _ (linearHomologyEquiv f g hfg)

include hf hg in
/-- If homology is finite over the coefficient ring, its high grades vanish. -/
theorem exists_bound_homologyGrade_eq_bot
    [Module.Finite R (CategoryTheory.ShortComplex.moduleCatMk f g hfg).homology] :
    ∃ b : ℕ, ∀ n ≥ b, homologyGrade NT f g hfg n = ⊥ := by
  let : Decomposition (homologyGrade NT f g hfg) :=
    (isInternal_homologyGrade NS NT NU f g hfg hf hg).chooseDecomposition
  exact HilbertSerre.exists_bound_grade_eq_bot _

include hf in
/-- If the homogeneous part of homology is zero, a homogeneous cycle is the
boundary of an element in the preceding coefficient grade. -/
theorem exists_boundary_in_grade_of_homologyGrade_eq_bot {k : ℕ} (hk : 0 < k)
    (hzero : homologyGrade NT f g hfg k = ⊥) (y : N)
    (hy : y ∈ NT k) (hgy : g y = 0) :
    ∃ z : M, z ∈ NS (k - 1) ∧ f z = y := by
  let c : g.ker := ⟨y, hgy⟩
  let a : LinearHomology f g hfg := (toCycles f g hfg).range.mkQ c
  have ha : a ∈ linearHomologyGrade NT f g hfg k :=
    ⟨c, hy, rfl⟩
  have hclass : linearHomologyEquiv f g hfg a = 0 := by
    have hmem : linearHomologyEquiv f g hfg a ∈ homologyGrade NT f g hfg k :=
      ⟨a, ha, rfl⟩
    rw [hzero, Submodule.mem_bot] at hmem
    exact hmem
  have hazero : a = 0 :=
    (linearHomologyEquiv f g hfg).injective (hclass.trans (map_zero _).symm)
  have hc : c ∈ (toCycles f g hfg).range :=
    (Submodule.Quotient.mk_eq_zero (p := (toCycles f g hfg).range) (x := c)).mp hazero
  obtain ⟨z, hz⟩ := hc
  have hfz : f z = y := congrArg Subtype.val hz
  refine ⟨gradeProjection NS (k - 1) z, (DirectSum.decompose NS z (k - 1)).2, ?_⟩
  have hp := DFunLike.congr_fun (gradeProjection_succ_comp NS NT f hf (k - 1)) z
  simp only [LinearMap.comp_apply] at hp
  rw [hfz, Nat.sub_add_cancel hk, gradeProjection_same NT k hy] at hp
  exact hp.symm

end homology

end SerrePositivity.GradedKoszul
