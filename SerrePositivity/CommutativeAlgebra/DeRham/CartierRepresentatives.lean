module

public import SerrePositivity.CommutativeAlgebra.DeRham.Polynomial
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import all SerrePositivity.CommutativeAlgebra.DeRham.Polynomial
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# Cartier 同型の代表元

## 概要
標数 p の多項式 de Rham 複体で、Frobenius と一次の Cartier 類の閉形式を与える。

## 方針
偏微分の冪公式と、一つの微分形式を二度外積すると零になることを用いる。

## 規約
一次の代表元は X の p−1 乗と dX の積。

## 使われ方
inverse Cartier と結晶側の生成元の照合。
-/

public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace SerrePositivity.DeRham

variable (k : Type u) [CommRing k] (T : Type u) [Fintype T] [DecidableEq T]

/-- 多項式 de Rham 余鎖複体の各項を微分形式で表す。 -/
def deRhamTerm (i : ℕ) : forms k T i ≃ₗ[k] (deRhamComplex k T).X i :=
  LinearEquiv.refl _ _

/-- 隣の次数への余鎖微分は、多項式形式の de Rham 微分である。 -/
theorem deRhamTerm_d (i : ℕ) (ω : forms k T i) :
    (deRhamComplex k T).d i (i+1) (deRhamTerm k T i ω) =
      deRhamTerm k T (i+1) (deRhamD k T i ω) := by
  dsimp only [deRhamComplex, deRhamTerm, CochainComplex.of]
  rw [CochainComplex.of_d]
  rfl

/-- 閉微分形式から de Rham コホモロジー類を取る。 -/
def deRhamClass (i : ℕ) (ω : forms k T i) (h : deRhamD k T i ω = 0) :
    (deRhamComplex k T).homology i :=
  let K := deRhamComplex k T
  K.homologyπ i (K.cyclesMk (deRhamTerm k T i ω) (i+1) (CochainComplex.next ℕ i) (by
    change K.d i (i+1) (deRhamTerm k T i ω) = 0
    rw [deRhamTerm_d, h, map_zero]))

private theorem formsZeroEquiv_tmul (f : Poly k T) :
    formsZeroEquiv k T f = f ⊗ₜ[k] (exteriorPower.zeroEquiv k (T → k)).symm 1 := by
  simp [formsZeroEquiv]

/-- 係数環で p が零なら、p 乗の微分は零。 -/
theorem cartierZero_closed (p : ℕ) (hp : (p : k) = 0) (f : Poly k T) :
    deRhamD k T 0 (formsZeroEquiv k T (f ^ p)) = 0 := by
  rw [formsZeroEquiv_tmul]
  simp only [deRhamD, deRhamDLinear, LinearMap.toAddMonoidHom_coe, LinearMap.sum_apply,
    TensorProduct.map_tmul]
  apply Finset.sum_eq_zero
  intro j _
  change MvPolynomial.pderiv j (f ^ p) ⊗ₜ[k] _ = 0
  rw [MvPolynomial.pderiv_pow, ← map_natCast (MvPolynomial.C : k →+* Poly k T),
    hp, map_zero, zero_mul, zero_mul, TensorProduct.zero_tmul]

omit [Fintype T] in
private theorem wedgeOne_dX_self (t : T) :
    let e := (exteriorPower.oneEquiv k (T → k)).symm (Pi.single t 1)
    wedgeOne k (T → k) 1 e e = 0 := by
  intro e
  apply Subtype.ext
  simp [e, exteriorPower.oneEquiv_symm_apply, ExteriorAlgebra.ιMulti_apply]

/-- 各変数の Cartier 一次形式は閉形式。 -/
theorem cartierOne_closed (p : ℕ) (t : T) :
    deRhamD k T 1 (((MvPolynomial.X t : Poly k T) ^ (p-1)) • dX k T t) = 0 := by
  change deRhamD k T 1 ((((MvPolynomial.X t : Poly k T) ^ (p-1)) * 1) ⊗ₜ[k] _) = 0
  simp only [mul_one, deRhamD, deRhamDLinear, LinearMap.toAddMonoidHom_coe, LinearMap.sum_apply,
    TensorProduct.map_tmul]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : j = t
  · subst j
    rw [wedgeOne_dX_self, TensorProduct.tmul_zero]
  · change MvPolynomial.pderiv j ((MvPolynomial.X t : Poly k T) ^ (p-1)) ⊗ₜ[k] _ = 0
    rw [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X, Pi.single_apply,
      ite_eq_right (Ne.symm h), mul_zero, TensorProduct.zero_tmul]

/-- Frobenius による次数零の Cartier 類。 -/
def cartierZeroClass (p : ℕ) (hp : (p : k) = 0) (f : Poly k T) :
    (deRhamComplex k T).homology 0 :=
  deRhamClass k T 0 (formsZeroEquiv k T (f ^ p)) (cartierZero_closed k T p hp f)

/-- 各変数に対応する次数一の Cartier 類。 -/
def cartierOneClass (p : ℕ) (t : T) : (deRhamComplex k T).homology 1 :=
  deRhamClass k T 1 (((MvPolynomial.X t : Poly k T) ^ (p-1)) • dX k T t) (cartierOne_closed k T p t)

end SerrePositivity.DeRham
