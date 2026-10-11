module

public import SerrePositivity.CommutativeAlgebra.GradedCumulativeGrowth
public import SerrePositivity.CommutativeAlgebra.HilbertSamuelPolynomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Cumulative graded lengths and Samuel functions

Summing the lengths of the Rees graded components below degree `n` gives the
Samuel length of `M/IⁿM`. Restricting scalars preserves an additive grading, so
the same graded Hilbert-series arguments apply to polynomial rings over residue
fields viewed as modules over their original local ring.
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity.HilbertSerre

/-- An additive decomposition is unchanged by restricting module scalars. -/
@[instance_reducible]
def decompositionRestrictScalars
    (R : Type u) [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (N : ℕ → Submodule S M) [DirectSum.Decomposition N] :
    DirectSum.Decomposition (fun n => (N n).restrictScalars R) where
  decompose' := DirectSum.decompose N
  left_inv := (DirectSum.decompose N).left_inv
  right_inv := (DirectSum.decompose N).right_inv

/-- The homogeneous polynomial grading is still a decomposition over a smaller scalar ring. -/
@[instance_reducible]
def homogeneousDecompositionRestrictScalars
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (σ : Type w) :
    DirectSum.Decomposition
      (fun n => (MvPolynomial.homogeneousSubmodule σ S n).restrictScalars R) := by
  let : DirectSum.Decomposition (MvPolynomial.homogeneousSubmodule σ S) :=
    MvPolynomial.decomposition
  exact decompositionRestrictScalars R (MvPolynomial.homogeneousSubmodule σ S)

end SerrePositivity.HilbertSerre

namespace SerrePositivity.HilbertSamuel

open IsLocalRing

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The cumulative series of the Rees grades is exactly the Samuel series. -/
theorem cumulativeSeries_reesGrade (hI : I.radical = maximalIdeal R) :
    HilbertSerre.cumulativeSeries (reesGrade R I M) = samuelSeries R I M := by
  rw [HilbertSerre.cumulativeSeries_eq, lengthSeries_reesGrade,
    ← samuelSeries_eq R I M hI]

/-- Summing all graded lengths below degree `n` gives the rational Samuel length. -/
theorem cumulativeLength_reesGrade (hI : I.radical = maximalIdeal R) (n : ℕ) :
    HilbertSerre.cumulativeLength (reesGrade R I M) n =
      ((samuelFunction R I M n).toNat : ℚ) := by
  have h := congrArg (PowerSeries.coeff n) (cumulativeSeries_reesGrade R I M hI)
  simpa only [HilbertSerre.cumulativeSeries, samuelSeries, PowerSeries.coeff_mk] using h

end SerrePositivity.HilbertSamuel
