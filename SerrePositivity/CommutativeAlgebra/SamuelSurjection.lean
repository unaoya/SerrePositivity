module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuelBasic
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Samuel functions under surjective module maps

Surjective linear maps induce surjections on the quotients by ideal powers.
We also construct the map from `(R/p)/x(R/p)` to `R/q` when `p ≤ q` and `x ∈ q`.
-/

@[expose] public section

universe u

open scoped Pointwise

namespace SerrePositivity.HilbertSamuel

variable {R M N : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A surjection induces a map on every Samuel quotient. -/
def samuelQuotientMap (I : Ideal R) (f : M →ₗ[R] N) (n : ℕ) :
    M ⧸ (I ^ n • ⊤ : Submodule R M) →ₗ[R]
      N ⧸ (I ^ n • ⊤ : Submodule R N) :=
  Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top (I ^ n) f)

/-- The map on Samuel quotients is surjective when the original map is. -/
lemma samuelQuotientMap_surjective (I : Ideal R) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (samuelQuotientMap I f n) := by
  intro y
  obtain ⟨y, rfl⟩ := (I ^ n • ⊤ : Submodule R N).mkQ_surjective y
  obtain ⟨z, rfl⟩ := hf y
  exact ⟨Submodule.Quotient.mk z, rfl⟩

/-- Surjections decrease Samuel functions, without any finiteness hypotheses. -/
lemma samuelFunction_le_of_surjective (I : Ideal R) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (n : ℕ) :
    samuelFunction R I N n ≤ samuelFunction R I M n :=
  Module.length_le_of_surjective (samuelQuotientMap I f n)
    (samuelQuotientMap_surjective I f hf n)

/-- If `p ≤ q` and `x ∈ q`, the canonical map `R/p → R/q` kills `x(R/p)`. -/
lemma pointwise_smul_top_le_ker_factor (p q : Ideal R) (hpq : p ≤ q)
    (x : R) (hx : x ∈ q) :
    (x • ⊤ : Submodule R (R ⧸ p)) ≤ LinearMap.ker (Submodule.factor hpq) := by
  rw [Submodule.pointwise_smul_def, Submodule.map_le_iff_le_comap]
  intro y _
  obtain ⟨r, rfl⟩ := p.mkQ_surjective y
  change (Submodule.Quotient.mk (x * r) : R ⧸ q) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact q.mul_mem_right r hx

/-- The canonical surjection after quotienting by a scalar that belongs to `q`. -/
def quotSMulTopToIdealQuotient (p q : Ideal R) (hpq : p ≤ q)
    (x : R) (hx : x ∈ q) : QuotSMulTop x (R ⧸ p) →ₗ[R] R ⧸ q :=
  (x • ⊤ : Submodule R (R ⧸ p)).liftQ (Submodule.factor hpq)
    (pointwise_smul_top_le_ker_factor p q hpq x hx)

/-- This canonical map is surjective. -/
lemma quotSMulTopToIdealQuotient_surjective (p q : Ideal R) (hpq : p ≤ q)
    (x : R) (hx : x ∈ q) :
    Function.Surjective (quotSMulTopToIdealQuotient p q hpq x hx) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.factor_surjective hpq y
  exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- The Samuel growth of `R/q` is bounded by that of `(R/p)/x(R/p)`. -/
lemma samuelFunction_idealQuotient_le_quotSMulTop (I p q : Ideal R) (hpq : p ≤ q)
    (x : R) (hx : x ∈ q) (n : ℕ) :
    samuelFunction R I (R ⧸ q) n ≤
      samuelFunction R I (QuotSMulTop x (R ⧸ p)) n :=
  samuelFunction_le_of_surjective I (quotSMulTopToIdealQuotient p q hpq x hx)
    (quotSMulTopToIdealQuotient_surjective p q hpq x hx) n

end SerrePositivity.HilbertSamuel
