module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# 局所環上の有限長加群

Lemma 3.4 の組成列による帰納法（`notes/lemma-3-4.md`）に使う補題。

- 局所環上の単純加群は剰余体 `A ⧸ m` と同型。
- `N ≤ M` で `M ⧸ N` が単純なら `length M = length N + 1`。
- 有限長加群は `m` の冪で消える。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]

/-- 局所環上の単純加群は剰余体 `A ⧸ m` と同型。 -/
lemma IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal [IsSimpleModule A M] :
    Nonempty (M ≃ₗ[A] A ⧸ maximalIdeal A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule A M›
  exact ⟨e.trans (Submodule.quotEquivOfEq I (maximalIdeal A) (eq_maximalIdeal hI))⟩

omit [IsLocalRing A] in
/-- `N ≤ M` で `M ⧸ N` が単純なら `length M = length N + 1`。 -/
lemma Module.length_eq_succ_of_isSimpleModule_quotient (N : Submodule A M)
    [IsSimpleModule A (M ⧸ N)] : Module.length A M = Module.length A N + 1 := by
  rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N), Module.length_eq_one A (M ⧸ N)]

/-- 有限長加群は `m` の冪で消える。 -/
lemma IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow (h : IsFiniteLength A M) :
    ∃ n : ℕ, Module.IsTorsionBySet A M ((maximalIdeal A) ^ n : Ideal A) := by
  induction h with
  | of_subsingleton => exact ⟨0, fun x _ ↦ Subsingleton.elim _ _⟩
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    obtain ⟨e⟩ :=
      IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal (A := A) (M := M ⧸ N)
    -- `m • M ⊆ N`：`M ⧸ N ≃ A ⧸ m` は `m` で消える
    have hmN : ∀ (c : A), c ∈ maximalIdeal A → ∀ x : M, c • x ∈ N := by
      intro c hc x
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      apply e.injective
      rw [map_smul, map_zero]
      obtain ⟨y, hy⟩ :=
        Submodule.Quotient.mk_surjective (maximalIdeal A) (e (Submodule.Quotient.mk x))
      rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mul_mem_right y _ hc
    intro x a
    obtain ⟨a, ha⟩ := a
    change a • x = 0
    have ha' : a ∈ maximalIdeal A ^ n * maximalIdeal A := by rw [← pow_succ]; exact ha
    refine Submodule.mul_induction_on ha' (fun b hb c hc ↦ ?_) (fun u v hu hv ↦ ?_)
    · -- `(b * c) • x = b • (c • x)`、`c • x ∈ N`、`N` は `m ^ n` で消える
      rw [mul_smul]
      have := @hn ⟨c • x, hmN c hc x⟩ ⟨b, hb⟩
      rw [Subtype.ext_iff] at this
      simpa using this
    · rw [add_smul, hu, hv, add_zero]

end SerrePositivity
