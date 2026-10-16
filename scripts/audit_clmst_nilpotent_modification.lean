import SerrePositivity.CommutativeAlgebra.PerfectoidizationNilpotent
import SerrePositivity.CommutativeAlgebra.PerfectoidIdealRadical
import SerrePositivity.CLMST.PerfectoidIdealRoots
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.IsPerfectoidization.precomp_surjective_nil_kernel
assert_no_sorry SerrePositivity.IsPerfectoidization.exists_equiv_of_surjective_nil_kernel
assert_no_sorry SerrePositivity.IsPerfectoidization.map_bijective_of_surjective_nil_kernel
assert_no_sorry SerrePositivity.IsPerfectoidization.map_bijective_quotient_of_le_radical
assert_no_sorry SerrePositivity.perfectoidIdeal_isRadical
assert_no_sorry SerrePositivity.radical_span_le_perfectoidIdeal
assert_no_sorry SerrePositivity.perfectoidIdeal_pow_eq
#print axioms SerrePositivity.IsPerfectoidization.precomp_surjective_nil_kernel
#print axioms SerrePositivity.IsPerfectoidization.exists_equiv_of_surjective_nil_kernel
#print axioms SerrePositivity.IsPerfectoidization.map_bijective_of_surjective_nil_kernel
#print axioms SerrePositivity.IsPerfectoidization.map_bijective_quotient_of_le_radical
#print axioms SerrePositivity.perfectoidIdeal_isRadical
#print axioms SerrePositivity.radical_span_le_perfectoidIdeal
#print axioms SerrePositivity.perfectoidIdeal_pow_eq

noncomputable section
universe u
open SerrePositivity
set_option backward.isDefEq.respectTransparency false

-- The actual B3 map for a power thickening is bijective and preserves every original scalar.
theorem audit_actual_power_quotient_comparison
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) (n : ℕ) (hn : 0 < n) :
    letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g ^ n}) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton (g ^ n))
    letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
    let hIJ : Ideal.span {g ^ n} ≤ Ideal.span {g} :=
      (Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) _ hn)
    let f := toQuotientPerfectoidization R (Ideal.span {g ^ n}) p hR
    let f' := toQuotientPerfectoidization R (Ideal.span {g}) p hR
    let hf := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g ^ n}) p hR
    let hf' := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR
    let q := Ideal.Quotient.factor hIJ
    Function.Bijective (IsPerfectoidization.map hf hf' q) ∧
      ∀ x : R, IsPerfectoidization.map hf hf' q (f (Ideal.Quotient.mk _ x)) =
        f' (Ideal.Quotient.mk _ x) := by
  dsimp only
  letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g ^ n}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton (g ^ n))
  letI : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  let hf := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g ^ n}) p hR
  let hf' := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR
  let hIJ : Ideal.span {g ^ n} ≤ Ideal.span {g} :=
    (Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) _ hn)
  constructor
  · apply IsPerfectoidization.map_bijective_quotient_of_le_radical R _ _ hIJ _ hf hf'
    intro x hx
    refine ⟨n, ?_⟩
    rw [← Ideal.span_singleton_pow]
    exact Ideal.pow_mem_pow hx n
  · intro x
    exact RingHom.congr_fun (IsPerfectoidization.map_comp hf hf'
      (Ideal.Quotient.factor hIJ)) (Ideal.Quotient.mk _ x)

-- Roots of an arbitrary original parameter now belong to the ideal without a reducedness input.
theorem audit_arbitrary_parameter_roots
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) (ρ : ℕ → R)
    (hρ : ∀ n, ρ n ^ (p ^ n) = g) :
    ∀ n, ρ n ∈ perfectoidIdeal R p hR g := by
  intro n
  apply radical_span_le_perfectoidIdeal R p hR g
  refine ⟨p ^ n, ?_⟩
  rw [hρ]
  exact Ideal.subset_span (Set.mem_singleton _)

assert_no_sorry audit_actual_power_quotient_comparison
assert_no_sorry audit_arbitrary_parameter_roots
#print axioms audit_actual_power_quotient_comparison
#print axioms audit_arbitrary_parameter_roots
assert_no_sorry SerrePositivity.CLMST.perfectoidQuotient_isReduced
#print axioms SerrePositivity.CLMST.perfectoidQuotient_isReduced
assert_no_sorry SerrePositivity.CLMST.mem_perfectoidIdeal_of_pow_mem_span
#print axioms SerrePositivity.CLMST.mem_perfectoidIdeal_of_pow_mem_span
assert_no_sorry SerrePositivity.CLMST.completedTowerRoot_mem_perfectoidIdeal
#print axioms SerrePositivity.CLMST.completedTowerRoot_mem_perfectoidIdeal
