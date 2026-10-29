module

public import SerrePositivity.CommutativeAlgebra.SamuelGrowthComparison
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Existence
public import SerrePositivity.CommutativeAlgebra.SamuelSurjection
public import SerrePositivity.CommutativeAlgebra.RegularSequence
public import SerrePositivity.CommutativeAlgebra.SamuelRegularGrowth

/-! # The degree of the Samuel polynomial and Krull dimension

The upper bound uses parameters inside a primary ideal. The lower bound uses
prime chains and the Artin–Rees growth estimate for a regular element.
-/

@[expose] public section

universe u

open Polynomial IsLocalRing Filter

namespace SerrePositivity.HilbertSamuel

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A generating family bounds the degree of the selected Samuel polynomial. -/
theorem natDegree_poly_le_of_generators (I : Ideal R)
    (hI : I.radical = maximalIdeal R) {s : ℕ} (x : Fin s → R)
    (hx : Ideal.span (Set.range x) = I)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (poly R I M).natDegree ≤ s := by
  obtain ⟨Q, hQ⟩ := exists_rational_hilbertSeries R I M hI x hx
  obtain ⟨P, hP, hdeg⟩ := exists_isSamuelPoly_of_hilbertSeries R I M hI s Q hQ
  rwa [poly_eq R hP]

/-- Parameters chosen inside `I` bound its Samuel degree by the ring dimension. -/
theorem natDegree_poly_le_dim (I : Ideal R) (hI : I.radical = maximalIdeal R) :
    (poly R I R).natDegree ≤ dimToNat (ringKrullDim R) := by
  obtain ⟨z, hz, hrad⟩ := exists_radical_span_eq_maximalIdeal_of_radical_eq R I hI
  let J := Ideal.span (Set.range z)
  have hJI : J ≤ I := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hz i)
  exact (natDegree_poly_antitone_of_le R J I hrad hI hJI).trans
    (natDegree_poly_le_of_generators R J hrad z rfl R)

/-- A prime quotient cannot have larger Samuel degree than the original ring. -/
theorem natDegree_poly_primeQuotient_le (I : Ideal R)
    (hI : I.radical = maximalIdeal R) (p : PrimeSpectrum R) :
    (poly R I (R ⧸ p.asIdeal)).natDegree ≤ (poly R I R).natDegree := by
  have hP := isSamuelPoly_poly_of_radical R I hI (R ⧸ p.asIdeal)
  have hQ := isSamuelPoly_poly_of_radical R I hI R
  apply PolynomialGrowth.natDegree_le_of_eventually_eval_le
    (hP.leadingCoeff_pos_of_nontrivial hI)
  filter_upwards [hP, hQ] with n hnP hnQ
  rw [← hnP.2, ← hnQ.2]
  exact_mod_cast ENat.toNat_le_toNat
    (samuelFunction_le_of_surjective I p.asIdeal.mkQ p.asIdeal.mkQ_surjective n) hnQ.1

/-- Strict inclusion of prime ideals strictly decreases the Samuel degree of their quotients. -/
theorem natDegree_poly_primeQuotient_lt (I : Ideal R)
    (hI : I.radical = maximalIdeal R) (p q : PrimeSpectrum R) (hpq : p < q) :
    (poly R I (R ⧸ q.asIdeal)).natDegree < (poly R I (R ⧸ p.asIdeal)).natDegree := by
  obtain ⟨x, hxq, hxp⟩ := Set.exists_of_ssubset
    (show (p.asIdeal : Set R) ⊂ q.asIdeal from hpq)
  exact (isSamuelPoly_poly_of_radical R I hI (R ⧸ p.asIdeal)).natDegree_lt_of_le_regular_quotient
    hI (isSamuelPoly_poly_of_radical R I hI (R ⧸ q.asIdeal)) x
    (isSMulRegular_quotient_of_notMem_prime p.asIdeal hxp)
    (samuelFunction_idealQuotient_le_quotSMulTop I p.asIdeal q.asIdeal hpq.le x hxq)

/-- Every strict prime chain is bounded by the Samuel degree of its initial prime quotient. -/
theorem primeChain_length_le_natDegree (I : Ideal R)
    (hI : I.radical = maximalIdeal R) (c : LTSeries (PrimeSpectrum R)) :
    c.length ≤ (poly R I (R ⧸ c.head.asIdeal)).natDegree := by
  induction c using RelSeries.inductionOn with
  | singleton p => simp
  | cons c p hp ih =>
    simp only [RelSeries.cons_length, RelSeries.head_cons]
    exact Nat.succ_le_of_lt (ih.trans_lt (natDegree_poly_primeQuotient_lt R I hI p c.head hp))

/-- Prime chains give the lower bound for the Samuel polynomial degree. -/
theorem dim_le_natDegree_poly (I : Ideal R) (hI : I.radical = maximalIdeal R) :
    dimToNat (ringKrullDim R) ≤ (poly R I R).natDegree := by
  have hdim : ringKrullDim R ≤ ((poly R I R).natDegree : WithBot ℕ∞) := by
    change (⨆ c : LTSeries (PrimeSpectrum R), (c.length : WithBot ℕ∞)) ≤ _
    refine iSup_le fun c => ?_
    exact_mod_cast (primeChain_length_le_natDegree R I hI c).trans
      (natDegree_poly_primeQuotient_le R I hI c.head)
  rw [← natCast_dimToNat_ringKrullDim R] at hdim
  exact_mod_cast hdim

/-- **Hilbert–Samuel dimension theorem**: the Samuel degree of the ring is its Krull
dimension (Atiyah–Macdonald, Theorem 11.14). Parameters give the upper bound;
Artin–Rees and induction on prime chains give the lower bound. -/
theorem natDegree_poly_eq_dim (I : Ideal R) (hI : I.radical = maximalIdeal R) :
    (poly R I R).natDegree = dimToNat (ringKrullDim R) :=
  le_antisymm (natDegree_poly_le_dim R I hI) (dim_le_natDegree_poly R I hI)

end SerrePositivity.HilbertSamuel
