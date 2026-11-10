module

public import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPDerivation
public import SerrePositivity.BhattScholze.Prismatic.PDPolynomialCech
public import SerrePositivity.CommutativeAlgebra.DeRham.Polynomial
import Mathlib.RingTheory.Derivation.Lie

/-!
# 未完備 pd de Rham 列の偏微分

## 概要
第 0 頂点の多項式座標と分冪差座標の偏微分を定める。

## 方針
係数の二つのテンソル因子の一方に偏微分を作用させる。

## 規約
差座標の偏微分は分冪の指数を一つ下げる。

## 使われ方
pd de Rham 微分と列の Poincaré 収縮。
-/

public noncomputable section

open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

/-- 第 0 頂点の座標と、他の頂点の第 0 頂点との差を添字付ける。 -/
abbrev pdCoordinates (r n : ℕ) := Fin r ⊕ (Fin r × Fin n)

variable (k : Type u) [CommRing k] (r n : ℕ)

local notation "S" => (Fin r × Fin n)
local notation "B" => MvPolynomial (Fin r) k
local notation "D" => DividedPowerAlgebra k (S →₀ k)

/-- 未完備 pd 係数環上の座標ごとの偏微分。 -/
def pdRawPartial : pdCoordinates r n → (pdRaw k r n →ₗ[k] pdRaw k r n)
  | .inl a => TensorProduct.map (MvPolynomial.pderiv a).toLinearMap LinearMap.id
  | .inr a => TensorProduct.map LinearMap.id (freeDPPartial a).toLinearMap

@[simp] private theorem partial_inl_tmul (a : Fin r) (f : B) (g : D) :
    pdRawPartial k r n (.inl a) (f ⊗ₜ[k] g) = MvPolynomial.pderiv a f ⊗ₜ[k] g :=
  TensorProduct.map_tmul _ _ _ _

@[simp] private theorem partial_inr_tmul (a : S) (f : B) (g : D) :
    pdRawPartial k r n (.inr a) (f ⊗ₜ[k] g) = f ⊗ₜ[k] freeDPPartial a g :=
  TensorProduct.map_tmul _ _ _ _

/-- 各座標での pd 偏微分は互いに可換。 -/
theorem pdRawPartial_comm (a b : pdCoordinates r n) (x : pdRaw k r n) :
    pdRawPartial k r n a (pdRawPartial k r n b x) =
      pdRawPartial k r n b (pdRawPartial k r n a x) := by
  let A := pdRawPartial k r n a
  let B' := pdRawPartial k r n b
  suffices h : A.comp B' = B'.comp A from DFunLike.congr_fun h x
  apply TensorProduct.ext'
  intro f g
  change pdRawPartial k r n a (pdRawPartial k r n b (f ⊗ₜ[k] g)) =
    pdRawPartial k r n b (pdRawPartial k r n a (f ⊗ₜ[k] g))
  rcases a with a | a <;> rcases b with b | b
  · simp only [partial_inl_tmul]
    have h : ⁅MvPolynomial.pderiv (R := k) a, MvPolynomial.pderiv (R := k) b⁆ = 0 := by
      apply MvPolynomial.derivation_ext
      intro t
      simp only [Derivation.commutator_apply, MvPolynomial.pderiv_X, Pi.single_apply]
      split <;> split <;> simp
    have e : MvPolynomial.pderiv a (MvPolynomial.pderiv b f) =
        MvPolynomial.pderiv b (MvPolynomial.pderiv a f) := by
      apply sub_eq_zero.mp
      simpa only [Derivation.commutator_apply, Derivation.zero_apply] using
        congrArg (fun d : Derivation k B B => d f) h
    rw [e]
  · simp
  · simp
  · simp only [partial_inr_tmul]
    rw [freeDPPartial_comm]

/-- 差座標の分冪に偏微分を施したときの値。 -/
theorem pdRawPartial_dp_succ (a : S) (m : ℕ) (x : S →₀ k) :
    pdRawPartial k r n (.inr a) ((1 : B) ⊗ₜ[k] DividedPowerAlgebra.dp k (m + 1) x) =
      (x a) • ((1 : B) ⊗ₜ[k] DividedPowerAlgebra.dp k m x) := by
  rw [partial_inr_tmul, freeDPPartial_dp_succ, TensorProduct.tmul_smul]

end SerrePositivity.BhattScholze.Prismatic
