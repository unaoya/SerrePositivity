import SerrePositivity.CLMST.PerfectoidIdealTorTransport
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.exists_scalar_inverse_of_ker_coker_annihilated
assert_no_sorry SerrePositivity.torCoefficientIdeal_eq_zero_iff_of_almost_comparison
assert_no_sorry SerrePositivity.torCoefficientScalar_eq_zero_of_reverse_finiteFree_almost_comparison
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_iff_of_almost_comparison
assert_no_sorry SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_reverse_finiteFree_comparison
#print axioms SerrePositivity.exists_scalar_inverse_of_ker_coker_annihilated
#print axioms SerrePositivity.torCoefficientIdeal_eq_zero_iff_of_almost_comparison
#print axioms SerrePositivity.torCoefficientScalar_eq_zero_of_reverse_finiteFree_almost_comparison
#print axioms SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_iff_of_almost_comparison
#print axioms SerrePositivity.CLMST.perfectoidIdeal_powerTorsionTorInput_of_reverse_finiteFree_comparison

noncomputable section
universe u
open SerrePositivity SerrePositivity.CLMST CategoryTheory
set_option backward.isDefEq.respectTransparency false

-- A span C → D ← E retains the original coefficient ideal actions on both ends.
theorem audit_tor_almost_span
    (R C D E : Type u) [CommRing R] [CommRing C] [CommRing D] [CommRing E]
    [Algebra R C] [Algebra R D] [Algebra R E] (I : Ideal R)
    (f : C →ₗ[R] D) (g : E →ₗ[R] D)
    (hfk : ∀ a ∈ I, ∀ x : f.ker, a • x = 0)
    (hfc : ∀ b ∈ I, ∀ y : D ⧸ f.range, b • y = 0)
    (hgk : ∀ a ∈ I, ∀ x : g.ker, a • x = 0)
    (hgc : ∀ b ∈ I, ∀ y : D ⧸ g.range, b • y = 0)
    (N : ModuleCat.{u} R) (a : R) (ha : ∀ x : N, a • x = 0)
    (hid : IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a})))) (i : ℕ) :
    (∀ s ∈ I, torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
      ∀ s ∈ I, torCoefficientScalarEndomorphism E N i (algebraMap R E s) = 0 := by
  exact (torCoefficientIdeal_eq_zero_iff_of_almost_comparison f I hfk hfc N a ha hid i).trans
    (torCoefficientIdeal_eq_zero_iff_of_almost_comparison g I hgk hgc N a ha hid i).symm

-- A rank-zero reverse comparison retains all power-torsion tests without Nontrivial C.
theorem audit_reverse_zero_rank_perfectoid_coefficient
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : R)
    (hC : ∀ s ∈ perfectoidIdeal R p hR g, ∀ x : C, s • x = 0) :
    ∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR g,
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0 := by
  let f : (Fin 0 → R) →ₗ[R] C := 0
  have hk : ∀ s ∈ perfectoidIdeal R p hR g, ∀ x : f.ker, s • x = 0 := by
    intro s hs x
    exact Subsingleton.elim _ _
  have hc : ∀ s ∈ perfectoidIdeal R p hR g, ∀ y : C ⧸ f.range, s • y = 0 := by
    intro s hs y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective f.range y
    rw [← map_smul, hC s hs x, map_zero]
  exact perfectoidIdeal_powerTorsionTorInput_of_reverse_finiteFree_comparison R p hR g C
    0 f hk hc

assert_no_sorry audit_tor_almost_span
assert_no_sorry audit_reverse_zero_rank_perfectoid_coefficient
#print axioms audit_tor_almost_span
#print axioms audit_reverse_zero_rank_perfectoid_coefficient
