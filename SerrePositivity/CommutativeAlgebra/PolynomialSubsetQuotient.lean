module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Quotient.Operations
/-!
# 変数部分族を零にする多項式商

## 概要
指定した変数集合を零にした多項式商は、残りの変数の多項式環。
## 方針
零への評価と残りの変数の包含を商上で両逆にする。
## 規約
BS 著者版 Proposition 7.10 の初期根のみを消す商への入力。
## 使われ方
有限関係商の自由性と、関係数によらないねじれの評価。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (J : Type v) (s : Set J)

/-- 指定した変数のみで生成されるイデアル。 -/
def polynomialSubsetIdeal : Ideal (MvPolynomial J R) :=
  Ideal.span (MvPolynomial.X '' s)

/-- 指定変数を零にし、他の変数をそのまま残す評価。 -/
def polynomialSubsetEvaluation : MvPolynomial J R →ₐ[R] MvPolynomial {j // j ∉ s} R := by
  classical
  exact MvPolynomial.aeval (fun j => if h : j ∈ s then 0 else MvPolynomial.X ⟨j, h⟩)

/-- 評価は、指定変数で割った商を経由する。 -/
def polynomialSubsetQuotientEvaluation :
    (MvPolynomial J R ⧸ polynomialSubsetIdeal R J s) →ₐ[R] MvPolynomial {j // j ∉ s} R :=
  Ideal.Quotient.liftₐ _ (polynomialSubsetEvaluation R J s) (by
    classical
    change polynomialSubsetIdeal R J s ≤ RingHom.ker (polynomialSubsetEvaluation R J s).toRingHom
    rw [polynomialSubsetIdeal, Ideal.span_le]
    rintro _ ⟨j, hj, rfl⟩
    simp [polynomialSubsetEvaluation, hj])

/-- 概要：変数部分族の零関係商は補変数の多項式環と代数同型。
方針：評価と rename を商上で比較し、各変数の像で両逆を示す。
規約：BS 著者版 Proposition 7.10。添字や関係の有限性は不要。
使われ方：生の根関係商の係数環上の自由基底。 -/
def polynomialSubsetQuotientEquiv :
    (MvPolynomial J R ⧸ polynomialSubsetIdeal R J s) ≃ₐ[R] MvPolynomial {j // j ∉ s} R := by
  classical
  let q := Ideal.Quotient.mkₐ R (polynomialSubsetIdeal R J s)
  let ev := polynomialSubsetQuotientEvaluation R J s
  let incl := q.comp (MvPolynomial.rename (Subtype.val : {j // j ∉ s} → J))
  apply AlgEquiv.ofAlgHom ev incl
  · apply MvPolynomial.algHom_ext
    intro j
    simp [ev, incl, q, polynomialSubsetQuotientEvaluation, polynomialSubsetEvaluation, j.property]
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j ∈ s
    · have hz : Ideal.Quotient.mk (polynomialSubsetIdeal R J s) (MvPolynomial.X j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, hj, rfl⟩)
      simpa [ev, incl, q, polynomialSubsetQuotientEvaluation, polynomialSubsetEvaluation, hj] using hz.symm
    · simp [ev, incl, q, polynomialSubsetQuotientEvaluation, polynomialSubsetEvaluation, hj]

end SerrePositivity
