module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPBaseChange
public import Mathlib.RingTheory.DividedPowers.RatAlgebra
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# 自由分冪代数の分冪単項式基底

## 概要
任意の可換環上で、有限台の分冪単項式が自由分冪代数の基底をなす。

## 方針
整数係数では有理係数の多項式環に評価して線形独立性を示す。
整数係数で得た基底を係数拡大同型で移す。

## 規約
変数集合は任意。分冪単項式の指数は有限台。

## 使われ方
分冪包の正則性と結晶の橋。
-/

public section
noncomputable section

universe u v

open scoped TensorProduct

namespace SerrePositivity.BhattScholze

variable (S : Type v)

section RationalEvaluation

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C] [Algebra ℚ C]

/-- 自由分冪代数を有理係数代数上の多項式環へ評価する射。 -/
def freeDPPolynomialEval : DividedPowerAlgebra A (S →₀ A) →ₐ[A] MvPolynomial S C := by
  classical
  exact DividedPowerAlgebra.lift (DividedPowers.RatAlgebra.dividedPowers ⊤)
    (Finsupp.linearCombination A MvPolynomial.X) (fun _ => Submodule.mem_top)

/-- 基底ベクトルの分冪は対応する変数の階乗逆数倍の冪へ移る。 -/
theorem freeDPPolynomialEval_dp (s : S) (n : ℕ) :
    freeDPPolynomialEval S A C (DividedPowerAlgebra.dp A n (Finsupp.single s 1)) =
      MvPolynomial.C (Ring.inverse (n.factorial : C)) * MvPolynomial.X s ^ n := by
  classical
  rw [freeDPPolynomialEval, DividedPowerAlgebra.lift_apply_dp, Finsupp.linearCombination_single,
    one_smul, DividedPowers.RatAlgebra.dpow_apply,
    ite_eq_left (Submodule.mem_top : MvPolynomial.X s ∈ _)]
  have h := (IsUnit.natCast_factorial_of_algebra ℚ n (A := C)).map_ringInverse
    (MvPolynomial.C : C →+* MvPolynomial S C)
  rw [map_natCast] at h
  rw [h]

private def factorialWeight (m : S →₀ ℕ) : C :=
  m.prod fun _ n => Ring.inverse (n.factorial : C)

private theorem freeDPPolynomialEval_monomial (m : S →₀ ℕ) :
    freeDPPolynomialEval S A C (freeDPMonomial S A m) =
      (factorialWeight S C m) • MvPolynomial.monomial m 1 := by
  unfold freeDPMonomial factorialWeight Finsupp.prod
  simp_rw [map_prod, freeDPPolynomialEval_dp, Finset.prod_mul_distrib,
    MvPolynomial.prod_X_pow_eq_monomial]
  rw [MvPolynomial.smul_eq_C_mul, map_prod]

private theorem isUnit_factorialWeight (m : S →₀ ℕ) : IsUnit (factorialWeight S C m) := by
  unfold factorialWeight Finsupp.prod
  exact IsUnit.prod_iff.mpr fun s _ => (IsUnit.natCast_factorial_of_algebra ℚ (m s)).ringInverse

private theorem freeDPPolynomialEval_linearIndependent
    (hAC : Function.Injective (algebraMap A C)) :
    LinearIndependent A ((freeDPPolynomialEval S A C).toLinearMap ∘ freeDPMonomial S A) := by
  have hc : LinearIndependent C ((freeDPPolynomialEval S A C).toLinearMap ∘ freeDPMonomial S A) := by
    let w (m : S →₀ ℕ) : Cˣ := (isUnit_factorialWeight S C m).unit
    have h := (MvPolynomial.basisMonomials S C).linearIndependent.units_smul w
    convert h using 1
    funext m
    change freeDPPolynomialEval S A C (freeDPMonomial S A m) =
      ((w m : C) • MvPolynomial.monomial m (1 : C))
    rw [freeDPPolynomialEval_monomial, IsUnit.unit_spec]
  exact hc.restrict_scalars (by simpa [Algebra.smul_def] using hAC)

/-- 係数写像が単射なら、自由分冪代数の多項式環への評価は単射。 -/
theorem freeDPPolynomialEval_injective (hAC : Function.Injective (algebraMap A C)) :
    Function.Injective (freeDPPolynomialEval S A C) :=
  LinearMap.injective_of_linearIndependent (freeDPMonomial_span S A)
    (freeDPPolynomialEval_linearIndependent S A C hAC)

end RationalEvaluation

private theorem freeDPMonomial_linearIndependent_int : LinearIndependent ℤ (freeDPMonomial S ℤ) :=
  LinearIndependent.of_comp (freeDPPolynomialEval S ℤ ℚ).toLinearMap
    (freeDPPolynomialEval_linearIndependent S ℤ ℚ Int.cast_injective)

private def intDPBasis : Module.Basis (S →₀ ℕ) ℤ (DividedPowerAlgebra ℤ (S →₀ ℤ)) :=
  Module.Basis.mk (freeDPMonomial_linearIndependent_int S) (by rw [freeDPMonomial_span])

/-- 概要：自由分冪代数の分冪単項式基底。
方針：整数係数の基底を標準係数拡大同型で移す。
規約：添字は変数集合上の有限台自然数値関数。
使われ方：自由変数分冪包とその係数拡大。 -/
def freeDPBasis (A : Type u) [CommRing A] :
    Module.Basis (S →₀ ℕ) A (DividedPowerAlgebra A (S →₀ A)) :=
  ((intDPBasis S).baseChange A).map (freeDPBaseChangeEquiv S ℤ A).toLinearEquiv

/-- 基底の各元は対応する分冪単項式に一致する。 -/
@[simp]
theorem freeDPBasis_apply (A : Type u) [CommRing A] (m : S →₀ ℕ) :
    freeDPBasis S A m = freeDPMonomial S A m := by
  rw [freeDPBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply, intDPBasis,
    Module.Basis.mk_apply, AlgEquiv.toLinearEquiv_apply, freeDPBaseChangeEquiv_apply,
    freeDPBaseChangeMap_monomial]

/-- 自由変数分冪代数では係数環の正則元の乗法が単射。 -/
theorem freeDP_isSMulRegular {A : Type u} [CommRing A] (a : A)
    (ha : Function.Injective (a * · : A → A)) :
    Function.Injective (a • · : DividedPowerAlgebra A (S →₀ A) → DividedPowerAlgebra A (S →₀ A)) := by
  intro x y h
  apply (freeDPBasis S A).repr.injective
  ext m
  apply ha
  simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using
    congrArg (fun z => (freeDPBasis S A).repr z m) h

end SerrePositivity.BhattScholze
