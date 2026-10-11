module

public import SerrePositivity.HomologicalAlgebra.AdicFilteredComplex
public import SerrePositivity.CommutativeAlgebra.AdicTermEuler
public import SerrePositivity.CommutativeAlgebra.FiniteLengthComplexEuler

/-! # Comparing an adic quotient Euler sum with the original complex -/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AdicEulerComparison

open CategoryTheory CategoryTheory.Limits IsLocalRing

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (P : CochainComplex (ModuleCat.{u} R) ℤ) (I : Ideal R)
variable (hd : ∀ q, (P.d q (q + 1)).hom.range ≤ I • ⊤)

omit [IsNoetherianRing R] [IsLocalRing R] in
theorem quotient_bounded (n : ℤ)
    (hb : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q)) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q →
      IsZero ((AdicFilteredComplex.quotient P I hd n).X q) := by
  obtain ⟨a, b, hab⟩ := hb
  refine ⟨a, b, fun q hq => ?_⟩
  let : Subsingleton (P.X q) := ModuleCat.isZero_iff_subsingleton.mp (hab q hq)
  change IsZero (ModuleCat.of R (P.X q ⧸ AdicFilteredComplex.term P I n q))
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

/-- Once the adic tail is acyclic, the ordinary Euler characteristic is the
alternating sum of lengths of the finite adic term quotients. -/
theorem chiOrd_eq_adicEuler (n : ℤ) (hI : I.radical = maximalIdeal R)
    (hf : ∀ q, Module.Finite R (P.X q))
    (hb : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (hacyclic : ∀ q, IsZero ((AdicFilteredComplex.tail P I hd n).homology q)) :
    chiOrd P = AdicTermEuler.euler P I n := by
  let f := AdicFilteredComplex.projection P I hd n
  let : QuasiIso f := AdicFilteredComplex.quasiIso_projection P I hd n hacyclic
  have hfin : ∀ q, IsFiniteLength R ((AdicFilteredComplex.quotient P I hd n).X q) := by
    intro q
    let : Module.Finite R (P.X q) := hf q
    exact AdicFilteredComplex.finiteLength_quotient_term P I hd hI q n
  calc
    chiOrd P = chiOrd (AdicFilteredComplex.quotient P I hd n) :=
      FiniteLengthComplexEuler.chiOrd_eq_of_quasiIso f
    _ = _ := by
      rw [FiniteLengthComplexEuler.chiOrd_eq_alternating_term_lengths _
        (quotient_bounded P I hd n hb) hfin]
      rfl

end SerrePositivity.AdicEulerComparison
