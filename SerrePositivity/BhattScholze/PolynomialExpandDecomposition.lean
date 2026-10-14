module

public import SerrePositivity.BhattScholze.PolynomialExponentDivMod
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # B4-6：expand射の単項式分解

指数の商・余りの同値で係数を付け替え、Mathlibのcurryでまとめる。
まだexpandを係数環とする自由加群の構造とは区別する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable (n : ℕ) (σ : Type u) (R : Type v) [CommRing R] (hn : 0 < n)

/-- 各指数がn未満の単項式で分類した、多項式の係数分解。 -/
def polynomialExpandDecomposition :
    MvPolynomial σ R ≃ₗ[R] PolynomialExponentRemainder n σ →₀ MvPolynomial σ R :=
  (AddMonoidAlgebra.coeffLinearEquiv R).trans
    ((Finsupp.lcongr (polynomialExponentDivModEquiv n σ hn) (LinearEquiv.refl R R)).trans
      ((Finsupp.curryLinearEquiv R).trans
        (Finsupp.lcongr (Equiv.refl _) (AddMonoidAlgebra.coeffLinearEquiv R).symm)))

/-- 逆分解は、余りbと商qの単項式をn*q+bの単項式へ戻す。 -/
@[simp] theorem polynomialExpandDecomposition_symm_single_monomial
    (b : PolynomialExponentRemainder n σ) (q : σ →₀ ℕ) (c : R) :
    (polynomialExpandDecomposition n σ R hn).symm
      (Finsupp.single b (MvPolynomial.monomial q c)) =
      MvPolynomial.monomial (n • q + b.val) c := by
  change (AddMonoidAlgebra.coeffLinearEquiv R).symm
    ((Finsupp.lcongr (polynomialExponentDivModEquiv n σ hn) (LinearEquiv.refl R R)).symm
      ((Finsupp.curryLinearEquiv R).symm
        ((Finsupp.lcongr (Equiv.refl (PolynomialExponentRemainder n σ))
          (AddMonoidAlgebra.coeffLinearEquiv R).symm).symm
            (Finsupp.single b (MvPolynomial.monomial q c))))) = _
  rw [Finsupp.lcongr_symm_single]
  change (AddMonoidAlgebra.coeffLinearEquiv R).symm
    ((Finsupp.lcongr (polynomialExponentDivModEquiv n σ hn) (LinearEquiv.refl R R)).symm
      ((Finsupp.curryLinearEquiv R).symm (Finsupp.single b (Finsupp.single q c)))) = _
  simp only [Finsupp.curryLinearEquiv_symm_apply, Finsupp.uncurry_single,
    Finsupp.lcongr_symm_single, polynomialExponentDivModEquiv_symm_apply]
  rfl

end SerrePositivity.BhattScholze
