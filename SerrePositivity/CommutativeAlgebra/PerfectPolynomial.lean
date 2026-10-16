module

public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.Basic
/-! # Free perfect polynomial algebras

The coefficient action is fixed through the ordinary polynomial inclusion.
Evaluation into a perfect characteristic-p algebra extends uniquely, and indexing
variables by all elements of the target supplies a surjective presentation.
Flatness over a perfect coefficient ring is proved separately.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p]

/-- The perfection of the polynomial ring on the specified variables. -/
abbrev PerfectPolynomial (σ : Type u) := PerfectClosure (MvPolynomial σ R) p

/-- The coefficient action through the standard polynomial inclusion. -/
instance perfectPolynomialAlgebra (σ : Type u) : Algebra R (PerfectPolynomial p R σ) :=
  ((PerfectClosure.of (MvPolynomial σ R) p).comp MvPolynomial.C).toAlgebra

/-- The perfect-closure lift preserves the original ring map. -/
lemma perfectClosure_lift_of {K S : Type u} [CommRing K] [CharP K p]
    [CommRing S] [CharP S p] [PerfectRing S p] (f : K →+* S) (x : K) :
    (PerfectClosure.lift K p S f) (PerfectClosure.of K p x) = f x := by
  exact congrArg (fun g : K →+* S => g x) ((PerfectClosure.lift K p S).symm_apply_apply f)

/-- Evaluation extends to the perfect closure as an R-algebra map. -/
def perfectPolynomialEval (σ S : Type u) [CommRing S] [Algebra R S]
    [CharP S p] [PerfectRing S p] (f : σ → S) : PerfectPolynomial p R σ →ₐ[R] S :=
  { PerfectClosure.lift (MvPolynomial σ R) p S (MvPolynomial.eval₂Hom (algebraMap R S) f) with
    commutes' := fun r => by
      change PerfectClosure.lift (MvPolynomial σ R) p S
        (MvPolynomial.eval₂Hom (algebraMap R S) f)
        (PerfectClosure.of (MvPolynomial σ R) p (MvPolynomial.C r)) = algebraMap R S r
      rw [perfectClosure_lift_of]
      exact MvPolynomial.eval₂_C _ _ _ }

/-- Evaluation sends each original variable to its prescribed value. -/
lemma perfectPolynomialEval_X (σ S : Type u) [CommRing S] [Algebra R S]
    [CharP S p] [PerfectRing S p] (f : σ → S) (s : σ) :
    perfectPolynomialEval p R σ S f
      (PerfectClosure.of (MvPolynomial σ R) p (MvPolynomial.X s)) = f s := by
  change PerfectClosure.lift (MvPolynomial σ R) p S
    (MvPolynomial.eval₂Hom (algebraMap R S) f)
    (PerfectClosure.of (MvPolynomial σ R) p (MvPolynomial.X s)) = f s
  rw [perfectClosure_lift_of]
  exact MvPolynomial.eval₂_X _ _ _

/-- Variables indexed by the target itself give a surjective presentation. -/
lemma perfectPolynomialEval_surjective (S : Type u) [CommRing S] [Algebra R S]
    [CharP S p] [PerfectRing S p] :
    Function.Surjective (perfectPolynomialEval p R S S id) := by
  intro s
  exact ⟨PerfectClosure.of (MvPolynomial S R) p (MvPolynomial.X s),
    perfectPolynomialEval_X p R S S id s⟩
/-- Maps to a perfect algebra are determined by their values on the variables. -/
lemma perfectPolynomial_hom_ext (σ S : Type u) [CommRing S] [Algebra R S]
    [CharP S p] [PerfectRing S p] {f g : PerfectPolynomial p R σ →ₐ[R] S}
    (h : ∀ s, f (PerfectClosure.of (MvPolynomial σ R) p (MvPolynomial.X s)) =
      g (PerfectClosure.of (MvPolynomial σ R) p (MvPolynomial.X s))) : f = g := by
  apply AlgHom.toRingHom_injective
  apply (PerfectClosure.lift (MvPolynomial σ R) p S).symm.injective
  apply MvPolynomial.ringHom_ext
  · intro r
    change f (algebraMap R (PerfectPolynomial p R σ) r) =
      g (algebraMap R (PerfectPolynomial p R σ) r)
    rw [f.commutes, g.commutes]
  · exact h

/-- The universal property of the free perfect polynomial algebra. -/
def perfectPolynomialHomEquiv (σ S : Type u) [CommRing S] [Algebra R S]
    [CharP S p] [PerfectRing S p] :
    (σ → S) ≃ (PerfectPolynomial p R σ →ₐ[R] S) where
  toFun := perfectPolynomialEval p R σ S
  invFun f s := f (PerfectClosure.of (MvPolynomial σ R) p (MvPolynomial.X s))
  left_inv f := by funext s; exact perfectPolynomialEval_X p R σ S f s
  right_inv f := by
    apply perfectPolynomial_hom_ext
    intro s
    exact perfectPolynomialEval_X p R σ S _ s

end SerrePositivity
