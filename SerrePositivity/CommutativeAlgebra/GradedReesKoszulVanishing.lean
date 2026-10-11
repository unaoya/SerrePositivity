module

public import SerrePositivity.CommutativeAlgebra.GradedKoszulVanishing
public import SerrePositivity.CommutativeAlgebra.ReesKoszulEvaluation

/-!
# Uniform homogeneous boundary lifting in Rees Koszul complexes

The polynomial-module Koszul vanishing theorem applies to the Rees module and
its coefficient grading. These concrete APIs feed the filtered Koszul tail
through evaluation at `t = 1`.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.ReesKoszulEvaluation

open CategoryTheory GradedKoszul

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I)

/-- The Rees differential raises coefficient degree by one. -/
theorem sourceTermGrade_differential (q : ℤ) (k : ℕ)
    (y : (underlyingComplex (R := R)
      (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (sourceModule R I z hz)).X q)
    (hy : y ∈ sourceTermGrade R I z hz q k) :
    ((underlyingComplex (R := R)
      (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (sourceModule R I z hz)).d
        q (q + 1)).hom y ∈ sourceTermGrade R I z hz (q + 1) (k + 1) :=
  differential_mem_termGrade MvPolynomial.X (sourceModule R I z hz)
    (sourceCoefficientGrade R I z hz)
    (sourceCoefficientGrade_variables_degree R I z hz) q k y hy

/-- In all sufficiently large coefficient degrees, homogeneous cycles in
the Rees Koszul complex have homogeneous primitives one degree lower. -/
theorem exists_uniform_bound_source_boundary [IsNoetherianRing R] :
    ∃ b : ℕ, 0 < b ∧ ∀ q : ℤ, ∀ k ≥ b,
      ∀ y : (underlyingComplex (R := R)
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (sourceModule R I z hz)).X q,
      y ∈ sourceTermGrade R I z hz q k →
      ((underlyingComplex (R := R)
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (sourceModule R I z hz)).d
          q (q + 1)).hom y = 0 →
      ∃ a : (underlyingComplex (R := R)
        (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (sourceModule R I z hz)).X (q - 1),
        a ∈ sourceTermGrade R I z hz (q - 1) (k - 1) ∧
          ((underlyingComplex (R := R)
            (MvPolynomial.X : Fin h → MvPolynomial (Fin h) R) (sourceModule R I z hz)).d
              (q - 1) q).hom a = y := by
  let : Module.Finite (MvPolynomial (Fin h) R) (sourceModule R I z hz) := by
    dsimp only [sourceModule]
    exact KoszulReesFinite.finite_reesPolynomialModule R I R z hz
  let : DirectSum.Decomposition (sourceCoefficientGrade R I z hz) :=
    (isInternal_sourceCoefficientGrade R I z hz).chooseDecomposition
  exact exists_uniform_bound_polynomialKoszul_boundary h (sourceModule R I z hz)
    (sourceCoefficientGrade R I z hz) (sourceCoefficientGrade_variables_degree R I z hz)

end SerrePositivity.ReesKoszulEvaluation
