module

public import SerrePositivity.KTheory.Adams.PolynomialNaturality
public import SerrePositivity.KTheory.Adams.LagrangeProjectors

/-! # Adams weight projectors before imposing regularity or height bounds -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
namespace Adams
variable {R : Type u} [CommRing R] {E : Type v} [Field E] [CharZero E] {p : ℕ}

lemma natPow_injective (hp : 2 ≤ p) : Function.Injective (fun j : ℕ => (p : E) ^ j) := by
  intro i j he
  change (p : E) ^ i = (p : E) ^ j at he
  have hn : p ^ i = p ^ j := by exact_mod_cast he
  exact Nat.pow_right_injective hp hn

def SupportedAdams.weightProjector (A : SupportedAdams R E p)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (c d j : ℕ) :
    Module.End E (K0WithSupport.Coefficients E Z) :=
  lagrangeProjector (Finset.Icc c d) (fun j => (p : E) ^ j) (A.operation Z) j

lemma SupportedAdams.sum_weightProjector (A : SupportedAdams R E p)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (c d : ℕ) (hc : c ≤ d)
    (x : K0WithSupport.Coefficients E Z) :
    (∑ j ∈ Finset.Icc c d, A.weightProjector Z c d j x) = x :=
  sum_lagrangeProjector _ _ _ (natPow_injective (E := E) A.two_le).injOn
    ⟨c, Finset.mem_Icc.mpr ⟨le_refl c, hc⟩⟩ x

omit [CharZero E] in
lemma SupportedAdams.weightProjector_enlarge (A : SupportedAdams R E p)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) (c d j : ℕ)
    (x : K0WithSupport.Coefficients E Z) :
    A.weightProjector W c d j (K0WithSupport.coefficientEnlarge E h x) =
      K0WithSupport.coefficientEnlarge E h (A.weightProjector Z c d j x) :=
  A.polynomial_enlarge h _ x

end Adams
end SerrePositivity
