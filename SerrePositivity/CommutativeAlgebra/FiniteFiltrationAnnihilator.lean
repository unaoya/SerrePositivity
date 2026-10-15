module
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Quotient.Defs
public import SerrePositivity.CommutativeAlgebra.IdempotentImageAnnihilator

/-! # Explicit ideal-power annihilator bounds from finite filtrations -/
@[expose] public section
open scoped Pointwise
namespace SerrePositivity
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An annihilator of a subquotient lowers scalar multiples of the upper submodule. -/
lemma ideal_smul_le_of_subquotient_annihilated (I : Ideal R) (U V : Submodule R M)
    (hI : I ≤ Module.annihilator R (V ⧸ U.comap V.subtype)) : I • V ≤ U := by
  rw [Submodule.smul_le]
  intro r hr x hx
  have h := Module.mem_annihilator.mp (hI hr) (Submodule.Quotient.mk (⟨x, hx⟩ : V))
  have hm : r • (⟨x, hx⟩ : V) ∈ U.comap V.subtype :=
    (Submodule.Quotient.mk_eq_zero _).mp (by
      simpa only [Submodule.Quotient.mk_smul] using h)
  exact hm

/-- Each multiplication lowers one filtration step, so the nth ideal power lowers n steps. -/
lemma ideal_pow_smul_finite_filtration_le (I : Ideal R) (F : ℕ → Submodule R M) (e : ℕ)
    (hstep : ∀ k : ℕ, k < e → I • F (k + 1) ≤ F k) (n : ℕ) :
    ∀ k : ℕ, k + n ≤ e → I ^ n • F (k + n) ≤ F k := by
  induction n with
  | zero => intro k _; simp
  | succ n ih =>
    intro k hk
    rw [pow_succ, Submodule.mul_smul, Nat.add_succ]
    calc
      I ^ n • (I • F (k + n + 1)) ≤ I ^ n • F (k + n) :=
        smul_mono_right _ (hstep (k + n) (by omega))
      _ ≤ F k := ih k (by omega)

/-- A filtration of e annihilated factors gives I^e annihilation, with no finiteness hypothesis. -/
lemma ideal_pow_annihilator_of_finite_filtration (I : Ideal R)
    (F : ℕ → Submodule R M) (e : ℕ) (hzero : F 0 = ⊥) (htop : F e = ⊤)
    (hstep : ∀ k : ℕ, k < e → I • F (k + 1) ≤ F k) :
    I ^ e ≤ Module.annihilator R M := by
  have h : I ^ e • (⊤ : Submodule R M) ≤ ⊥ := by
    simpa only [Nat.zero_add, hzero, htop] using
      ideal_pow_smul_finite_filtration_le I F e hstep e 0 (by omega)
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  exact (Submodule.mem_bot R).mp (h (Submodule.smul_mem_smul hr (Submodule.mem_top : x ∈ ⊤)))

/-- Annihilation of the actual successive subquotients gives the same explicit exponent. -/
lemma ideal_pow_annihilator_of_finite_quotient_filtration (I : Ideal R)
    (F : ℕ → Submodule R M) (e : ℕ) (hzero : F 0 = ⊥) (htop : F e = ⊤)
    (hquot : ∀ k : ℕ, k < e →
      I ≤ Module.annihilator R (F (k + 1) ⧸ (F k).comap (F (k + 1)).subtype)) :
    I ^ e ≤ Module.annihilator R M :=
  ideal_pow_annihilator_of_finite_filtration I F e hzero htop
    (fun k hk => ideal_smul_le_of_subquotient_annihilated I (F k) (F (k + 1)) (hquot k hk))

/-- The KL5 idempotent-image criterion removes the exponent on torsion modules. -/
lemma ideal_annihilator_of_finite_quotient_filtration_and_powerTorsion
    (I : Ideal R) (a : R)
    (hI : ∀ n : ℕ, 0 < n →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (F : ℕ → Submodule R M) (e : ℕ) (he : 0 < e) (hzero : F 0 = ⊥) (htop : F e = ⊤)
    (hquot : ∀ k : ℕ, k < e →
      I ≤ Module.annihilator R (F (k + 1) ⧸ (F k).comap (F (k + 1)).subtype))
    (ht : ∀ x : M, ∃ n : ℕ, a ^ n • x = 0) : I ≤ Module.annihilator R M := by
  have hpow := ideal_pow_annihilator_of_finite_quotient_filtration I F e hzero htop hquot
  intro r hr
  rw [Module.mem_annihilator]
  exact ideal_annihilates_of_pow_annihilates_and_powerTorsion I a hI e he
    (fun s hs x => Module.mem_annihilator.mp (hpow hs) x) ht r hr

end SerrePositivity
