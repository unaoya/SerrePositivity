module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Logic.Equiv.Option
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-! # 非零指数の通常冪根関係の正則性

任意の係数環で、指定した変数のモニック冪関係式は非零因子となる。
δ構造や指数の素数性は要求しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

/-- 非零指数の指定変数の冪根関係は、任意係数環上で非零因子。 -/
theorem monicPowerFamilyRelation_isSMulRegular {n : ℕ} {R : Type u} [CommRing R]
    {σ : Type v} (hn : n ≠ 0) (c : σ → R) (s : σ) :
    IsSMulRegular (MvPolynomial σ R) (MvPolynomial.X s ^ n - MvPolynomial.C (c s)) := by
  classical
  let e := (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe s).symm).trans
    (MvPolynomial.optionEquivLeft R {t : σ // t ≠ s})
  have he : e (MvPolynomial.X s ^ n - MvPolynomial.C (c s)) =
      Polynomial.X ^ n - Polynomial.C (MvPolynomial.C (c s)) := by
    simp [e, MvPolynomial.renameEquiv]
  have h := (Polynomial.monic_X_pow_sub_C
    (MvPolynomial.C (c s) : MvPolynomial {t : σ // t ≠ s} R) hn).isRegular.left
  intro x y hxy
  apply e.injective
  apply h
  have hh := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using hh

end SerrePositivity.BhattScholze
