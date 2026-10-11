module

public import SerrePositivity.CommutativeAlgebra.AdicEulerComparison
public import SerrePositivity.CommutativeAlgebra.KoszulAdicEuler
public import SerrePositivity.CommutativeAlgebra.ReesKoszulAcyclic

/-! # The Euler and polynomial part of the Koszul multiplicity formula

An eventually acyclic adic tail identifies Koszul homology with that of a
finite-length quotient complex. Its term Euler sum is the Samuel finite difference.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KoszulMultiplicityProof

open CategoryTheory CategoryTheory.Limits Filter

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The filtered comparison and the Samuel polynomial computation give multiplicity.
The tail acyclicity is supplied by the Rees Koszul construction. -/
theorem multiplicity_eq_chiOrd_of_eventually_acyclic_adicTail
    {h : ℕ} (z : Fin h → R) (hz : IsSystemOfParameters R z)
    (hd : ∀ q, ((koszulComplex z).d q (q + 1)).hom.range ≤
      Ideal.span (Set.range z) • ⊤)
    (hacyclic : ∀ᶠ n : ℕ in atTop, ∀ q,
      IsZero ((AdicFilteredComplex.tail (koszulComplex z) (Ideal.span (Set.range z)) hd
        (n : ℤ)).homology q)) :
    (HilbertSamuel.multiplicity R (Ideal.span (Set.range z)) R : ℝ) =
      chiOrd (koszulComplex z) := by
  obtain ⟨n, hn, hvalue⟩ :=
    (hacyclic.and (KoszulAdicEuler.eventually_euler_koszul_eq_multiplicity z hz)).exists
  have hf : ∀ q, Module.Finite R ((koszulComplex z).X q) :=
    fun q => (koszulComplex_free_finite_X z q).2
  have hb : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((koszulComplex z).X q) :=
    ⟨-(h : ℤ), 0, fun q hq => hq.elim
      (koszulComplex_isZero_X_of_lt z q) (koszulComplex_isZero_X_of_pos z q)⟩
  exact ((AdicEulerComparison.chiOrd_eq_adicEuler (koszulComplex z)
    (Ideal.span (Set.range z)) hd n hz.2 hf hb hn).trans hvalue).symm

/-- The parameter-ideal multiplicity equals the ordinary Koszul Euler characteristic.
All filtered acyclicity and numerical inputs are supplied by the Rees construction. -/
theorem multiplicity_eq_chiOrd_koszul {h : ℕ} (z : Fin h → R)
    (hz : IsSystemOfParameters R z) :
    (HilbertSamuel.multiplicity R (Ideal.span (Set.range z)) R : ℝ) =
      chiOrd (koszulComplex z) :=
  multiplicity_eq_chiOrd_of_eventually_acyclic_adicTail z hz
    (ReesKoszulAcyclic.differential_range_le R (Ideal.span (Set.range z)) z rfl)
    (ReesKoszulAcyclic.eventually_adicTail_acyclic R (Ideal.span (Set.range z)) z rfl)

end SerrePositivity.KoszulMultiplicityProof
