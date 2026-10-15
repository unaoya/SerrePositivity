module
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Localization torsion and uniform annihilators of finite modules -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open scoped TensorProduct
variable {R : Type u} [CommRing R]

/-- Every element is killed by an element of the multiplicative set. -/
def IsModuleSTorsion (P : Submonoid R) (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∀ m : M, ∃ r ∈ P, r • m = 0

namespace IsModuleSTorsion
variable {P : Submonoid R} {M N L : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup L] [Module R L]

lemma iff_localized_zero : IsModuleSTorsion P M ↔ Subsingleton (LocalizedModule P M) :=
  LocalizedModule.subsingleton_iff.symm

lemma of_injective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (h : IsModuleSTorsion P N) : IsModuleSTorsion P M := by
  intro m
  obtain ⟨r, hr, he⟩ := h (f m)
  exact ⟨r, hr, hf (by simpa using he)⟩

lemma of_surjective (g : M →ₗ[R] N) (hg : Function.Surjective g)
    (h : IsModuleSTorsion P M) : IsModuleSTorsion P N := by
  intro n
  obtain ⟨m, rfl⟩ := hg n
  obtain ⟨r, hr, he⟩ := h m
  exact ⟨r, hr, by simpa using congrArg g he⟩

lemma of_exact (f : M →ₗ[R] N) (g : N →ₗ[R] L) (he : Function.Exact f g)
    (hM : IsModuleSTorsion P M) (hL : IsModuleSTorsion P L) :
    IsModuleSTorsion P N := by
  intro n
  obtain ⟨r, hr, er⟩ := hL (g n)
  have hk : g (r • n) = 0 := by simpa using er
  obtain ⟨m, hm⟩ := (he (r • n)).mp hk
  obtain ⟨s, hs, es⟩ := hM m
  refine ⟨s * r, P.mul_mem hs hr, ?_⟩
  rw [mul_smul, ← hm, ← map_smul, es, map_zero]

lemma submodule (h : IsModuleSTorsion P M) (U : Submodule R M) :
    IsModuleSTorsion P U := of_injective U.subtype U.subtype_injective h

lemma quotient (h : IsModuleSTorsion P M) (U : Submodule R M) :
    IsModuleSTorsion P (M ⧸ U) := of_surjective U.mkQ U.mkQ_surjective h

lemma of_subsingleton [Subsingleton M] : IsModuleSTorsion P M :=
  fun _ => ⟨1, P.one_mem, Subsingleton.elim _ _⟩

lemma of_zero_mem (h : (0 : R) ∈ P) : IsModuleSTorsion P M :=
  fun m => ⟨0, h, zero_smul R m⟩

/-- Torsion is equivalent to the tensor model of localization being zero. -/
lemma iff_tensor_zero (B : Type u) [CommRing B] [Algebra R B] [IsLocalization P B] :
    IsModuleSTorsion P M ↔ Subsingleton (B ⊗[R] M) :=
  (IsLocalizedModule.subsingleton_iff P (TensorProduct.mk R B M 1)).symm
end IsModuleSTorsion

variable {P : Submonoid R} {M : Type u} [AddCommGroup M] [Module R M]

/-- The public elementwise predicate agrees with Mathlib's subtype-valued S-torsion. -/
lemma IsModuleSTorsion.iff_mathlib_isTorsion : IsModuleSTorsion P M ↔ Module.IsTorsion' M P := by
  constructor
  · intro h m
    obtain ⟨r, hr, he⟩ := h m
    exact ⟨⟨r, hr⟩, he⟩
  · intro h m
    obtain ⟨r, hr⟩ := h (x := m)
    exact ⟨r.val, r.property, hr⟩

namespace IsModuleSTorsion
/-- A finite set of torsion elements admits a common annihilator in the multiplicative set. -/
lemma exists_annihilator_finset (h : IsModuleSTorsion P M) (t : Finset M) :
    ∃ r ∈ P, ∀ m ∈ t, r • m = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, P.one_mem, by simp⟩
  | @insert m t hm ih =>
    obtain ⟨r, hr, er⟩ := h m
    obtain ⟨s, hs, es⟩ := ih
    refine ⟨s * r, P.mul_mem hs hr, ?_⟩
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · simp [mul_smul, er]
    · rw [mul_comm, mul_smul, es n hn, smul_zero]

/-- Finite generation turns elementwise torsion into a uniform annihilator. -/
lemma exists_annihilating_mem [Module.Finite R M] (h : IsModuleSTorsion P M) :
    ∃ r ∈ P, ∀ m : M, r • m = 0 := by
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := R) (M := M)
  obtain ⟨r, hr, er⟩ := h.exists_annihilator_finset t
  refine ⟨r, hr, fun m => ?_⟩
  have hm : m ∈ Submodule.span R (t : Set M) := by rw [ht]; trivial
  induction hm using Submodule.span_induction with
  | mem m hm => exact er m hm
  | zero => exact smul_zero r
  | add m n hm hn em en => simp [smul_add, em, en]
  | smul a m hm em => rw [smul_comm, em, smul_zero]

lemma iff_exists_annihilating_mem [Module.Finite R M] :
    IsModuleSTorsion P M ↔ ∃ r ∈ P, ∀ m : M, r • m = 0 :=
  ⟨exists_annihilating_mem, fun ⟨r, hr, er⟩ m => ⟨r, hr, er m⟩⟩
end IsModuleSTorsion

/-- A zero localization of a finite module admits a single annihilator. -/
lemma exists_annihilating_mem_of_localized_zero [Module.Finite R M]
    (h : Subsingleton (LocalizedModule P M)) : ∃ r ∈ P, ∀ m : M, r • m = 0 :=
  (IsModuleSTorsion.iff_localized_zero.mpr h).exists_annihilating_mem

end SerrePositivity
